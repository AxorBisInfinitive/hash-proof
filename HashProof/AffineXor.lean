import Std

namespace HashProof

open BitVec

/-- All masks for which XOR with the mask is affine modulo 2^32. -/
def affineMasks : List (BitVec 32) :=
  [0#32, intMin 32, intMax 32, allOnes 32]

private theorem add_eq_xor_of_and_zero {x y : BitVec w} (h : x &&& y = 0#w) :
    x + y = x ^^^ y := by
  rw [add_eq_or_of_and_eq_zero x y h]
  apply eq_of_getLsbD_eq
  intro i _
  have hi := congrArg (fun v : BitVec w => v.getLsbD i) h
  simp only [getLsbD_and, getLsbD_zero] at hi
  simp only [getLsbD_or, getLsbD_xor]
  cases hx : x.getLsbD i <;> cases hy : y.getLsbD i <;> simp_all

private theorem xor_one_slope (x : BitVec 32) :
    (1#32 ^^^ x) - x = 1#32 ∨ (1#32 ^^^ x) - x = -1#32 := by
  have add_if_even (v : BitVec 32) (h : v.getLsbD 0 = false) :
      v + 1#32 = 1#32 ^^^ v := by
    rw [xor_comm]
    apply add_eq_xor_of_and_zero
    rw [and_one_eq_setWidth_ofBool_getLsbD, h]
    decide +kernel
  cases h : x.getLsbD 0
  · exact Or.inl (eq_sub_iff_add_eq.mpr (by
      rw [BitVec.add_comm, add_if_even x h])).symm
  · right
    have he : (1#32 ^^^ x).getLsbD 0 = false := by
      rw [getLsbD_xor, h]
      decide +kernel
    have hadd : (1#32 ^^^ x) + 1#32 = x := by
      rw [add_if_even _ he, ← xor_assoc]
      simp
    apply sub_eq_iff_eq_add.mpr
    calc
      1#32 ^^^ x = ((1#32 ^^^ x) + 1#32) + (-1#32) := by
        rw [BitVec.add_assoc, BitVec.add_right_neg, BitVec.add_zero]
      _ = x + (-1#32) := by rw [hadd]
      _ = (-1#32) + x := BitVec.add_comm _ _

theorem xor_intMin (x : BitVec 32) :
    x ^^^ intMin 32 = x + intMin 32 := by
  have add_if_high_clear (v : BitVec 32) (h : v.getLsbD 31 = false) :
      v + intMin 32 = v ^^^ intMin 32 := by
    apply add_eq_xor_of_and_zero
    apply eq_of_getLsbD_eq
    intro i _
    by_cases hi : i = 31
    · subst i
      rw [getLsbD_and, h, getLsbD_zero]
      rfl
    · simp only [getLsbD_and, getLsbD_intMin, getLsbD_zero,
        show i + 1 ≠ 32 by omega, decide_false, Bool.and_false]
  cases h : x.getLsbD 31
  · exact (add_if_high_clear x h).symm
  · have hc : (x ^^^ intMin 32).getLsbD 31 = false := by
      rw [getLsbD_xor, getLsbD_intMin, h]
      decide +kernel
    have hx : (x ^^^ intMin 32) + intMin 32 = x := by
      rw [add_if_high_clear _ hc, xor_assoc]
      simp
    have hsum : intMin 32 + intMin 32 = 0#32 := by decide +kernel
    calc
      x ^^^ intMin 32 = ((x ^^^ intMin 32) + intMin 32) + intMin 32 := by
        rw [BitVec.add_assoc, hsum, BitVec.add_zero]
      _ = x + intMin 32 := by rw [hx]

private theorem neg_mul_add_allOnes (u : BitVec 32) :
    (-1#32) * u + allOnes 32 = u ^^^ allOnes 32 := by
  rw [xor_allOnes, ← allOnes_sub_eq_not, BitVec.sub_eq_add_neg,
    BitVec.add_comm (allOnes 32), neg_eq_neg_one_mul u]

/-- The full classification, with (u,t,s,C) represented as unsigned 32-bit words. -/
theorem affine_xor_iff (t s C : BitVec 32) :
    (∀ u : BitVec 32, t * u + s = u ^^^ C) ↔
      s = C ∧ ((t = 1#32 ∧ (C = 0#32 ∨ C = intMin 32)) ∨
               (t = -1#32 ∧ (C = intMax 32 ∨ C = allOnes 32))) := by
  constructor
  · intro h
    have hs : s = C := by simpa using h (0#32)
    subst s
    refine ⟨rfl, ?_⟩
    -- The inputs 1 and -1 determine the slope and twice the mask.
    have ht : t = (1#32 ^^^ C) - C := eq_sub_iff_add_eq.mpr (by simpa using h (1#32))
    have hneg := h (-1#32)
    rw [BitVec.mul_neg, BitVec.mul_one, neg_one_eq_allOnes, allOnes_xor, not_eq_neg_add] at hneg
    have he : -t + C + 1#32 = -C := (sub_eq_iff_eq_add.mp hneg.symm).symm
    have hdouble : C + C = t - 1#32 := by
      apply eq_sub_iff_add_eq.mpr
      calc
        (C + C) + 1#32 = t + (-t + C + 1#32) + C := by
          calc
            (C + C) + 1#32 = (t + -t) + ((C + 1#32) + C) := by
              rw [BitVec.add_right_neg, BitVec.zero_add]
              ac_rfl
            _ = t + (-t + C + 1#32) + C := by ac_rfl
        _ = t := by rw [he, BitVec.add_assoc, BitVec.add_left_neg, BitVec.add_zero]
    have hd := congrArg BitVec.toNat hdouble
    have hbound : C.toNat < 4294967296 := C.isLt
    have hexact (n : Nat) (hn : C.toNat = n) (hfit : n < 2^32) : C = BitVec.ofNat 32 n := by
      apply eq_of_toNat_eq
      rw [toNat_ofNat, Nat.mod_eq_of_lt hfit, hn]
    rcases xor_one_slope C with hpos | hneg
    · have ht' := ht.trans hpos
      refine Or.inl ⟨ht', ?_⟩
      rw [ht', BitVec.sub_self, toNat_add] at hd
      change (C.toNat + C.toNat) % 4294967296 = 0 at hd
      have hc : C.toNat = 0 ∨ C.toNat = 2147483648 := by omega
      rcases hc with hc | hc
      · exact Or.inl (hexact 0 hc (by decide))
      · exact Or.inr (hexact 2147483648 hc (by decide))
    · have ht' := ht.trans hneg
      refine Or.inr ⟨ht', ?_⟩
      rw [ht', toNat_add] at hd
      change (C.toNat + C.toNat) % 4294967296 = 4294967294 at hd
      have hc : C.toNat = 2147483647 ∨ C.toNat = 4294967295 := by omega
      rcases hc with hc | hc
      · exact Or.inl (hexact 2147483647 hc (by decide))
      · exact Or.inr (hexact 4294967295 hc (by decide))
  · rintro ⟨rfl, ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩⟩ u
    · simp
    · rw [BitVec.one_mul, xor_intMin]
    · have hmask : intMax 32 = allOnes 32 ^^^ intMin 32 := by decide +kernel
      have hsum : allOnes 32 + intMin 32 = intMax 32 := by decide +kernel
      calc
        (-1#32) * u + intMax 32 = ((-1#32) * u + allOnes 32) + intMin 32 := by
          rw [BitVec.add_assoc, hsum]
        _ = (u ^^^ allOnes 32) + intMin 32 := by rw [neg_mul_add_allOnes]
        _ = u ^^^ intMax 32 := by rw [hmask, ← xor_assoc, xor_intMin]
    · exact neg_mul_add_allOnes u

theorem affine_xor_mask {t s C : BitVec 32} (h : ∀ u, t * u + s = u ^^^ C) :
    C ∈ affineMasks := by
  rcases ((affine_xor_iff t s C).mp h).2 with ⟨_, rfl | rfl⟩ | ⟨_, rfl | rfl⟩ <;>
    simp [affineMasks]

end HashProof
