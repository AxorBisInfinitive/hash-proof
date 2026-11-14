import HashProof.AffineXor
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

end HashProof
