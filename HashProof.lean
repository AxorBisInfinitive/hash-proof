import HashProof.AffineXor
import HashProof.Difference
import HashProof.Mix

namespace HashProof

/-- The high half stores y and the low half stores z before XOR with H(x). -/
def hash (x y z : BitVec 32) : BitVec 64 := pack y z ^^^ H x

def nonzeroDeltas : List (BitVec 64) :=
  (affineMasks.flatMap fun hi => affineMasks.map (pack hi)).filter (· != 0#64)

theorem nonzeroDeltas_length : nonzeroDeltas.length = 15 := by decide +kernel

theorem nonzeroDeltas_nodup : nonzeroDeltas.Nodup := by decide +kernel

private theorem pack_mem_nonzeroDeltas {hi lo : BitVec 32}
    (hhi : hi ∈ affineMasks) (hlo : lo ∈ affineMasks) (hnz : pack hi lo ≠ 0#64) :
    pack hi lo ∈ nonzeroDeltas := by
  apply List.mem_filter.mpr
  exact ⟨List.mem_flatMap_of_mem hhi (List.mem_map_of_mem (f := pack hi) hlo), by simpa using hnz⟩

private theorem nonzeroDeltas_check :
    nonzeroDeltas.all (fun delta => decide (high32 (unmix64 delta) ≠ 0#32)) = true := by
  decide +kernel

/-- Phase 2 of the C verifier, checked by kernel reduction on the 15 masks. -/
theorem nonzeroDeltas_not_in_image {delta : BitVec 64} (hmem : delta ∈ nonzeroDeltas) :
    ¬ ∃ x : BitVec 32, H x = delta := by
  have hhi : high32 (unmix64 delta) ≠ 0#32 :=
    of_decide_eq_true ((List.all_eq_true.mp nonzeroDeltas_check) delta hmem)
  exact fun himage => hhi ((mem_image_H_iff delta).mp himage)

theorem no_nontrivial_affine_collision
    (a b c i j k : BitVec 32)
    (h : ∀ x y z : BitVec 32,
      hash (a * x + i) (b * y + j) (c * z + k) = hash x y z) :
    a = 1 ∧ b = 1 ∧ c = 1 ∧ i = 0 ∧ j = 0 ∧ k = 0 := by
  -- Set y = z = 0 to identify the constant XOR difference on the x axis.
  let delta := pack j k
  have hx (x : BitVec 32) : delta ^^^ H (a * x + i) = H x := by
    simpa [hash, delta, pack] using h x 0#32 0#32
  have hi : H i = delta := by
    have hi₀ : delta ^^^ H i = 0#64 := by simpa using hx 0#32
    exact (BitVec.xor_eq_zero_iff.mp hi₀).symm

  -- Set x = 0 and project the packed equality onto each 32-bit half.
  have hyz (y z : BitVec 32) :
      pack (b * y + j) (c * z + k) = pack y z ^^^ delta := by
    have hp : pack (b * y + j) (c * z + k) ^^^ delta = pack y z := by
      simpa [hash, hi] using h 0#32 y z
    simpa [BitVec.xor_assoc] using congrArg (· ^^^ delta) hp
  have hy (y : BitVec 32) : b * y + j = y ^^^ j := by
    simpa only [delta, pack_xor, high32_pack] using congrArg high32 (hyz y 0#32)
  have hz (z : BitVec 32) : c * z + k = z ^^^ k := by
    simpa only [delta, pack_xor, low32_pack] using congrArg low32 (hyz 0#32 z)

  have hdelta : delta = 0#64 := by
    apply Decidable.byContradiction
    intro hnz
    have hmem := pack_mem_nonzeroDeltas (affine_xor_mask hy) (affine_xor_mask hz) hnz
    exact nonzeroDeltas_not_in_image hmem ⟨i, hi⟩

  have hj : j = 0#32 := by
    simpa only [delta, high32_pack, high32_zero] using congrArg high32 hdelta
  have hk : k = 0#32 := by
    simpa only [delta, low32_pack, low32_zero] using congrArg low32 hdelta
  have hax (x : BitVec 32) : a * x + i = x :=
    H_injective (by simpa [hdelta] using hx x)
  have hi₀ : i = 0#32 := by simpa using hax 0#32
  have ha : a = 1#32 := by simpa [hi₀] using hax 1#32
  have hb : b = 1#32 := by simpa [hj] using hy 1#32
  have hc : c = 1#32 := by simpa [hk] using hz 1#32
  exact ⟨ha, hb, hc, hi₀, hj, hk⟩

abbrev Vec3 := Fin 3 → BitVec 32

abbrev Mat3 := Fin 3 → Fin 3 → BitVec 32

def identityMatrix : Mat3 := fun i j => if i = j then 1#32 else 0#32

private def affineRow (A : Mat3) (t : Vec3) (i : Fin 3) (x y z : BitVec 32) : BitVec 32 :=
  A i 0 * x + A i 1 * y + A i 2 * z + t i

def affineApply (A : Mat3) (t v : Vec3) : Vec3 :=
  fun i => affineRow A t i (v 0) (v 1) (v 2)

def hashVec (v : Vec3) : BitVec 64 := hash (v 0) (v 1) (v 2)

private theorem high32_xor (a b : BitVec 64) : high32 (a ^^^ b) = high32 a ^^^ high32 b :=
  BitVec.extractLsb'_xor

private theorem low32_xor (a b : BitVec 64) : low32 (a ^^^ b) = low32 a ^^^ low32 b :=
  BitVec.extractLsb'_xor

private theorem hash_xor_shift (x x' y z a b : BitVec 32) :
    hash x' (y + a * topBit) (z + b * topBit) ^^^ hash x y z =
      pack (a * topBit) (b * topBit) ^^^ (H x' ^^^ H x) := by
  unfold hash
  calc
    _ = (pack (y + a * topBit) (z + b * topBit) ^^^ pack y z) ^^^ (H x' ^^^ H x) := by
      ac_rfl
    _ = _ := by rw [pack_xor, xor_add_mul_topBit, xor_add_mul_topBit]

private theorem no_topBit_cross (p : BitVec 32 → BitVec 32) (a b c : BitVec 32)
    (hzero : p topBit ^^^ p 0#32 ≠ 0#32) (htop : p topBit ^^^ p 0#32 ≠ topBit)
    (h : ∀ u : BitVec 32, (a * u + b) ^^^ p (topBit * u) = c) : False := by
  have h0 := h 0#32
  have h1 := h 1#32
  have h2 := h 2#32
  have hq2 : topBit * 2#32 = 0#32 := by decide +kernel
  simp only [BitVec.mul_zero, BitVec.zero_add, BitVec.mul_one, hq2] at h0 h1 h2
  have hadd : a * 2#32 + b = b := (BitVec.xor_left_inj _).mp (h2.trans h0.symm)
  have hdouble : a + a = 0#32 := by
    simpa only [BitVec.mul_two, BitVec.add_sub_cancel, BitVec.sub_self] using
      congrArg (· - b) hadd
  have hxor : (a + b) ^^^ b = p topBit ^^^ p 0#32 := by
    apply BitVec.xor_eq_zero_iff.mp
    calc
      _ = ((a + b) ^^^ p topBit) ^^^ (b ^^^ p 0#32) := by ac_rfl
      _ = 0#32 := by rw [h1, h0, BitVec.xor_self]
  rcases eq_zero_or_topBit_of_double_zero hdouble with rfl | rfl
  · exact hzero (by simpa using hxor.symm)
  · have hmask : (topBit + b) ^^^ b = topBit := by
      simpa only [BitVec.one_mul, BitVec.add_comm b topBit] using xor_add_mul_topBit b 1#32
    exact htop (hxor.symm.trans hmask)

private theorem firstRow_cross_zero (A : Mat3) (t : Vec3)
    (h : ∀ x y z : BitVec 32,
      hash (affineRow A t 0 x y z) (affineRow A t 1 x y z) (affineRow A t 2 x y z) =
        hash x y z) : A 0 1 = 0#32 ∧ A 0 2 = 0#32 := by
  let row := affineRow A t
  have hshift (i : Fin 3) (x y z : BitVec 32) :
      row i (x + topBit) y z = row i x y z + A i 0 * topBit := by
    dsimp only [row, affineRow]
    rw [BitVec.mul_add]
    ac_rfl
  have hdiff (x y z : BitVec 32) :
      pack (A 1 0 * topBit) (A 2 0 * topBit) ^^^
        (H (row 0 x y z + A 0 0 * topBit) ^^^ H (row 0 x y z)) = topBitDiff x := by
    have h₁ := h (x + topBit) y z
    have h₀ := h x y z
    change hash (row 0 (x + topBit) y z) (row 1 (x + topBit) y z)
      (row 2 (x + topBit) y z) = hash (x + topBit) y z at h₁
    change hash (row 0 x y z) (row 1 x y z) (row 2 x y z) = hash x y z at h₀
    rw [← hash_xor_shift, ← hshift, ← hshift, ← hshift, h₁, h₀]
    unfold topBitDiff hash
    calc
      _ = (pack y z ^^^ pack y z) ^^^ (H (x + topBit) ^^^ H x) := by ac_rfl
      _ = _ := by simp
  have hodd : (A 0 0).toNat % 2 ≠ 0 := by
    intro heven
    have hconstant (x : BitVec 32) :
        pack (A 1 0 * topBit) (A 2 0 * topBit) = topBitDiff x := by
      simpa only [mul_topBit (A 0 0), ite_eq_left heven, BitVec.add_zero, BitVec.xor_self,
        BitVec.xor_zero] using hdiff x 0#32 0#32
    exact topBitDiff_not_constant ((hconstant _).symm.trans (hconstant _))
  have hshiftDiff (x y z : BitVec 32) :
      pack (A 1 0 * topBit) (A 2 0 * topBit) ^^^ topBitDiff (row 0 x y z) = topBitDiff x := by
    simpa only [mul_topBit (A 0 0), ite_eq_right hodd, topBitDiff] using hdiff x y z
  have hsurj := odd_mul_add_surjective (A 0 0) (t 0) hodd
  have hcandidates (y z : BitVec 32) :
      A 0 1 * y + A 0 2 * z = 0#32 ∨ A 0 1 * y + A 0 2 * z = topBit := by
    apply (topBitDiff_period_iff _).mp
    intro s
    obtain ⟨x, hx⟩ := hsurj s
    have hrow : row 0 x y z = s + (A 0 1 * y + A 0 2 * z) := by
      rw [← hx]
      dsimp only [row, affineRow]
      ac_rfl
    have hbase : row 0 x 0#32 0#32 = s := by
      simpa only [row, affineRow, BitVec.mul_zero, BitVec.add_zero] using hx
    have he := (BitVec.xor_right_inj _).mp ((hshiftDiff x y z).trans (hshiftDiff x 0#32 0#32).symm)
    simpa only [hrow, hbase] using he
  have hy : A 0 1 = 0#32 ∨ A 0 1 = topBit := by simpa using hcandidates 1#32 0#32
  have hz : A 0 2 = 0#32 ∨ A 0 2 = topBit := by simpa using hcandidates 0#32 1#32
  obtain ⟨x, hx⟩ := hsurj 0#32
  constructor
  · rcases hy with hy | hy
    · exact hy
    · exfalso
      have hlow := low32_topBitDiff_zero
      rw [topBitDiff, BitVec.zero_add, low32_xor] at hlow
      apply no_topBit_cross (fun s => low32 (H s)) (A 2 1) (A 2 0 * x + t 2)
        (low32 (H x)) hlow.1 hlow.2
      intro u
      have hrow : affineRow A t 0 x u 0#32 = topBit * u := by
        calc
          _ = topBit * u + (A 0 0 * x + t 0) := by
            simp only [affineRow, hy, BitVec.mul_zero, BitVec.add_zero]
            ac_rfl
          _ = _ := by rw [hx, BitVec.add_zero]
      have hother : affineRow A t 2 x u 0#32 = A 2 1 * u + (A 2 0 * x + t 2) := by
        simp only [affineRow, BitVec.mul_zero, BitVec.add_zero]
        ac_rfl
      simpa only [hash, low32_xor, low32_pack, BitVec.zero_xor, hrow, hother] using
        congrArg low32 (h x u 0#32)
  · rcases hz with hz | hz
    · exact hz
    · exfalso
      have hhigh := high32_topBitDiff_zero
      rw [topBitDiff, BitVec.zero_add, high32_xor] at hhigh
      apply no_topBit_cross (fun s => high32 (H s)) (A 1 2) (A 1 0 * x + t 1)
        (high32 (H x)) hhigh.1 hhigh.2
      intro u
      have hrow : affineRow A t 0 x 0#32 u = topBit * u := by
        calc
          _ = topBit * u + (A 0 0 * x + t 0) := by
            simp only [affineRow, hz, BitVec.mul_zero, BitVec.add_zero]
            ac_rfl
          _ = _ := by rw [hx, BitVec.add_zero]
      have hother : affineRow A t 1 x 0#32 u = A 1 2 * u + (A 1 0 * x + t 1) := by
        simp only [affineRow, BitVec.mul_zero, BitVec.add_zero]
        ac_rfl
      simpa only [hash, high32_xor, high32_pack, BitVec.zero_xor, hrow, hother] using
        congrArg high32 (h x 0#32 u)

private theorem xor_eq_xor_flip {a b c d : BitVec 32} (h : a ^^^ b = c ^^^ d) :
    a = c ^^^ (b ^^^ d) := by
  simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero, BitVec.xor_comm d b] using
    congrArg (· ^^^ b) h

private theorem affine_xor_addend_of_slope_one {s C : BitVec 32}
    (h : ∀ u : BitVec 32, 1#32 * u + s = u ^^^ C) : s = 0#32 ∨ s = topBit := by
  obtain ⟨rfl, ⟨_, hmask⟩ | ⟨hneg, _⟩⟩ := (affine_xor_iff 1#32 s C).mp h
  · exact hmask
  · exact False.elim ((by decide +kernel : 1#32 ≠ -1#32) hneg)

private theorem topBits_zero_of_H_one_xor_in_image {j k : BitVec 32}
    (hj : j = 0#32 ∨ j = topBit) (hk : k = 0#32 ∨ k = topBit)
    (h : ∃ x : BitVec 32, H x = H 1#32 ^^^ pack j k) : j = 0#32 ∧ k = 0#32 := by
  have himage := (mem_image_H_iff _).mp h
  rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
  · exact ⟨rfl, rfl⟩
  all_goals exact False.elim ((by decide +kernel : ¬ _) himage)

private theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have hi : i.val < 3 := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  exact h.imp Fin.ext (Or.imp Fin.ext Fin.ext)

/-- A hash-preserving affine map on three 32-bit coordinates is the identity. -/
theorem no_nontrivial_general_affine_collision
    (A : Mat3) (t : Vec3)
    (h : ∀ v : Vec3, hashVec (affineApply A t v) = hashVec v) :
    A = identityMatrix ∧ t = (fun _ => 0#32) := by
  have hscalar (x y z : BitVec 32) :
      hash (affineRow A t 0 x y z) (affineRow A t 1 x y z) (affineRow A t 2 x y z) =
        hash x y z := by
    let v : Vec3 := Fin.cases x (Fin.cases y (fun _ => z))
    exact h v
  obtain ⟨h01, h02⟩ := firstRow_cross_zero A t hscalar
  have hrow0 (x y z : BitVec 32) : affineRow A t 0 x y z = A 0 0 * x + t 0 := by
    simp only [affineRow, h01, h02, BitVec.zero_mul, BitVec.add_zero]
  have hy (x y : BitVec 32) : A 1 1 * y + (A 1 0 * x + t 1) =
      y ^^^ (high32 (H (A 0 0 * x + t 0)) ^^^ high32 (H x)) := by
    have hhalf := congrArg high32 (hscalar x y 0#32)
    simp only [hash, high32_xor, high32_pack, hrow0] at hhalf
    calc
      _ = affineRow A t 1 x y 0#32 := by
        simp only [affineRow, BitVec.mul_zero, BitVec.add_zero]
        ac_rfl
      _ = _ := xor_eq_xor_flip hhalf
  have hz (x z : BitVec 32) : A 2 2 * z + (A 2 0 * x + t 2) =
      z ^^^ (low32 (H (A 0 0 * x + t 0)) ^^^ low32 (H x)) := by
    have hhalf := congrArg low32 (hscalar x 0#32 z)
    simp only [hash, low32_xor, low32_pack, hrow0] at hhalf
    calc
      _ = affineRow A t 2 x 0#32 z := by
        simp only [affineRow, BitVec.mul_zero, BitVec.add_zero]
        ac_rfl
      _ = _ := xor_eq_xor_flip hhalf

  -- At the origin, the translation must give one of the already excluded masks.
  have hpack0 : pack 0#32 0#32 = 0#64 := by decide +kernel
  have htH : H (t 0) = pack (t 1) (t 2) := by
    have hzero : pack (t 1) (t 2) ^^^ H (t 0) = 0#64 := by
      simpa only [affineRow, BitVec.mul_zero, BitVec.zero_add, hash, H_zero, hpack0,
        BitVec.xor_zero] using hscalar 0#32 0#32 0#32
    exact (BitVec.xor_eq_zero_iff.mp hzero).symm
  have htmask1 : t 1 ∈ affineMasks := by
    simpa only [BitVec.mul_zero, BitVec.zero_add, htH, H_zero, high32_pack, high32_zero,
      BitVec.xor_zero] using affine_xor_mask (hy 0#32)
  have htmask2 : t 2 ∈ affineMasks := by
    simpa only [BitVec.mul_zero, BitVec.zero_add, htH, H_zero, low32_pack, low32_zero,
      BitVec.xor_zero] using affine_xor_mask (hz 0#32)
  have hdelta : pack (t 1) (t 2) = 0#64 := by
    apply Decidable.byContradiction
    intro hnonzero
    exact nonzeroDeltas_not_in_image (pack_mem_nonzeroDeltas htmask1 htmask2 hnonzero) ⟨t 0, htH⟩
  have ht0 : t 0 = 0#32 := H_injective (htH.trans (hdelta.trans H_zero.symm))
  have ht1 : t 1 = 0#32 := by simpa only [high32_pack, high32_zero] using congrArg high32 hdelta
  have ht2 : t 2 = 0#32 := by simpa only [low32_pack, low32_zero] using congrArg low32 hdelta

  -- The y and z basis vectors determine the lower-right block.
  have hblock (y z : BitVec 32) :
      pack (A 1 1 * y + A 1 2 * z) (A 2 1 * y + A 2 2 * z) = pack y z := by
    simpa only [hash, affineRow, h01, h02, ht0, ht1, ht2, BitVec.mul_zero, BitVec.zero_mul,
      BitVec.zero_add, BitVec.add_zero, H_zero, BitVec.xor_zero] using hscalar 0#32 y z
  have h11 : A 1 1 = 1#32 := by simpa using congrArg high32 (hblock 1#32 0#32)
  have h12 : A 1 2 = 0#32 := by simpa using congrArg high32 (hblock 0#32 1#32)
  have h21 : A 2 1 = 0#32 := by simpa using congrArg low32 (hblock 1#32 0#32)
  have h22 : A 2 2 = 1#32 := by simpa using congrArg low32 (hblock 0#32 1#32)

  -- Each remaining cross coefficient is a mask for an affine-XOR map of slope 1.
  have hm10 : A 1 0 = 0#32 ∨ A 1 0 = topBit := by
    have hmask := affine_xor_addend_of_slope_one (by simpa only [h11] using hy 1#32)
    simpa only [ht1, BitVec.mul_one, BitVec.add_zero] using hmask
  have hm20 : A 2 0 = 0#32 ∨ A 2 0 = topBit := by
    have hmask := affine_xor_addend_of_slope_one (by simpa only [h22] using hz 1#32)
    simpa only [ht2, BitVec.mul_one, BitVec.add_zero] using hmask
  have hone : pack (A 1 0) (A 2 0) ^^^ H (A 0 0) = H 1#32 := by
    simpa only [hash, affineRow, ht0, ht1, ht2, BitVec.mul_one, BitVec.mul_zero,
      BitVec.add_zero, hpack0, BitVec.zero_xor] using hscalar 1#32 0#32 0#32
  have hh : H (A 0 0) = H 1#32 ^^^ pack (A 1 0) (A 2 0) := by
    have hswap := (BitVec.xor_comm _ _).trans hone
    simpa only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero] using
      congrArg (· ^^^ pack (A 1 0) (A 2 0)) hswap
  obtain ⟨h10, h20⟩ := topBits_zero_of_H_one_xor_in_image hm10 hm20 ⟨A 0 0, hh⟩
  have h00 : A 0 0 = 1#32 := H_injective (by simpa only [h10, h20, hpack0, BitVec.xor_zero] using hh)

  constructor
  · funext i j
    rcases fin3_cases i with rfl | rfl | rfl <;> rcases fin3_cases j with rfl | rfl | rfl <;>
      simp [identityMatrix, h00, h01, h02, h10, h11, h12, h20, h21, h22]
  · funext i
    rcases fin3_cases i with rfl | rfl | rfl
    · exact ht0
    · exact ht1
    · exact ht2

end HashProof
