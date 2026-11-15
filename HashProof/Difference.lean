import HashProof.AffineXor
import HashProof.Mix

namespace HashProof

def topBit : BitVec 32 := BitVec.intMin 32

def topBitDiff (x : BitVec 32) : BitVec 64 := H (x + topBit) ^^^ H x

theorem mul_topBit (x : BitVec 32) :
    x * topBit = if x.toNat % 2 = 0 then 0#32 else topBit := by
  split <;> rename_i h <;> apply BitVec.eq_of_toNat_eq <;> rw [BitVec.toNat_mul]
  · change (x.toNat * 2147483648) % 4294967296 = 0
    omega
  · change (x.toNat * 2147483648) % 4294967296 = 2147483648
    omega

theorem xor_add_mul_topBit (x a : BitVec 32) :
    (x + a * topBit) ^^^ x = a * topBit := by
  rw [mul_topBit]
  split
  · simp
  · rw [show x + topBit = x ^^^ topBit from (xor_intMin x).symm]
    simp [BitVec.xor_comm x topBit, BitVec.xor_assoc]

private theorem lift_odd_mul (a b : Int) (ha : a % 2 = 1) (n : Nat) :
    ∃ x k : Int, a * x = b + 2 ^ n * k := by
  induction n with
  | zero => exact ⟨0, -b, by simp [Int.add_right_neg]⟩
  | succ n ih =>
    obtain ⟨x, k, hx⟩ := ih
    -- Choose the next bit of x so the error is divisible by 2^(n+1).
    by_cases hk : k % 2 = 0
    · refine ⟨x, k / 2, ?_⟩
      rw [Int.pow_succ, Int.mul_assoc, show 2 * (k / 2) = k by omega]
      exact hx
    · refine ⟨x + 2 ^ n, (k + a) / 2, ?_⟩
      rw [Int.pow_succ, Int.mul_assoc, show 2 * ((k + a) / 2) = k + a by omega]
      rw [Int.mul_add, hx, Int.add_assoc, Int.mul_comm a, Int.mul_add]

theorem odd_mul_add_surjective (a t : BitVec 32) (ha : a.toNat % 2 ≠ 0) :
    ∀ s : BitVec 32, ∃ x : BitVec 32, a * x + t = s := by
  intro s
  have ha' : (a.toNat : Int) % 2 = 1 := by omega
  obtain ⟨x, k, hx⟩ := lift_odd_mul a.toNat (s - t).toNat ha' 32
  have h := congrArg (BitVec.ofInt 32) hx
  change BitVec.ofInt 32 (↑a.toNat * x) =
    BitVec.ofInt 32 (↑(s - t).toNat + 2 ^ 32 * k) at h
  have cast_word (word : BitVec 32) : BitVec.ofInt 32 (word.toNat : Int) = word := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      (BitVec.ofInt_natCast 32 word.toNat)
  have hmod : BitVec.ofInt 32 (2 ^ 32) = 0#32 := by decide +kernel
  simp only [BitVec.ofInt_mul, BitVec.ofInt_add, cast_word, hmod,
    BitVec.zero_mul, BitVec.add_zero] at h
  exact ⟨BitVec.ofInt 32 x, BitVec.eq_sub_iff_add_eq.mp h⟩

private def IsTopBitDiffPeriod (d : BitVec 32) : Prop :=
  ∀ x : BitVec 32, topBitDiff (x + d) = topBitDiff x

private theorem period_add {d e : BitVec 32}
    (hd : IsTopBitDiffPeriod d) (he : IsTopBitDiffPeriod e) :
    IsTopBitDiffPeriod (d + e) := by
  intro x
  rw [← BitVec.add_assoc, he, hd]

private theorem topBitDiff_topBit : IsTopBitDiffPeriod topBit := by
  intro x
  have h : topBit + topBit = 0#32 := by decide +kernel
  change H ((x + topBit) + topBit) ^^^ H (x + topBit) = H (x + topBit) ^^^ H x
  rw [BitVec.add_assoc, h, BitVec.add_zero, BitVec.xor_comm]

theorem topBitDiff_not_constant : topBitDiff 0x40000000 ≠ topBitDiff 0#32 := by
  decide +kernel

theorem eq_zero_or_topBit_of_double_zero {d : BitVec 32} (h : d + d = 0#32) :
    d = 0#32 ∨ d = topBit := by
  have hbound : d.toNat < 4294967296 := d.isLt
  have hnat := congrArg BitVec.toNat h
  change (d.toNat + d.toNat) % 4294967296 = 0 at hnat
  have hd : d.toNat = 0 ∨ d.toNat = 2147483648 := by omega
  exact hd.imp BitVec.eq_of_toNat_eq BitVec.eq_of_toNat_eq

private theorem period_of_double {d : BitVec 32} (hd : IsTopBitDiffPeriod d)
    (h : d + d = 0#32 ∨ d + d = topBit) : d = 0#32 ∨ d = topBit := by
  rcases h with hzero | htop
  · exact eq_zero_or_topBit_of_double_zero hzero
  · have hbound : d.toNat < 4294967296 := d.isLt
    have hnat := congrArg BitVec.toNat htop
    change (d.toNat + d.toNat) % 4294967296 = 2147483648 at hnat
    have hd' : d.toNat = 1073741824 ∨ d.toNat = 3221225472 := by omega
    -- Either d or 3d is the excluded quarter-turn period.
    have hquarter : IsTopBitDiffPeriod (0x40000000 : BitVec 32) := by
      rcases hd' with hp | hp
      · have he : d = 0x40000000 := BitVec.eq_of_toNat_eq hp
        exact he ▸ hd
      · have he : d + d + d = 0x40000000 := by
          have he : d = 0xC0000000 := BitVec.eq_of_toNat_eq hp
          rw [he]
          decide +kernel
        exact he ▸ period_add (period_add hd hd) hd
    exact False.elim (topBitDiff_not_constant (by simpa using hquarter 0))

private theorem period_of_iterated_double (n : Nat) (d : BitVec 32)
    (hd : IsTopBitDiffPeriod d)
    (h : BitVec.ofNat 32 (2 ^ n) * d = 0#32 ∨ BitVec.ofNat 32 (2 ^ n) * d = topBit) :
    d = 0#32 ∨ d = topBit := by
  induction n generalizing d with
  | zero => simpa using h
  | succ n ih =>
    apply period_of_double hd (ih (d + d) (period_add hd hd) ?_)
    simpa only [Nat.pow_succ, BitVec.ofNat_mul, BitVec.mul_assoc, BitVec.two_mul] using h

private theorem eq_zero_or_topBit_of_period {d : BitVec 32} (hd : IsTopBitDiffPeriod d) :
    d = 0#32 ∨ d = topBit := by
  apply period_of_iterated_double 31 d hd
  change topBit * d = 0#32 ∨ topBit * d = topBit
  rw [BitVec.mul_comm topBit, mul_topBit]
  split <;> simp

theorem topBitDiff_period_iff (d : BitVec 32) :
    (∀ x : BitVec 32, topBitDiff (x + d) = topBitDiff x) ↔ d = 0#32 ∨ d = topBit := by
  constructor
  · exact eq_zero_or_topBit_of_period
  · rintro (rfl | rfl)
    · simp
    · exact topBitDiff_topBit

theorem high32_topBitDiff_zero :
    high32 (topBitDiff 0#32) ≠ 0#32 ∧ high32 (topBitDiff 0#32) ≠ topBit := by
  decide +kernel

theorem low32_topBitDiff_zero :
    low32 (topBitDiff 0#32) ≠ 0#32 ∧ low32 (topBitDiff 0#32) ≠ topBit := by
  decide +kernel

end HashProof
