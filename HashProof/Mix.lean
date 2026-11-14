import Std

namespace HashProof

def pack (hi lo : BitVec 32) : BitVec 64 := hi ++ lo

def high32 (v : BitVec 64) : BitVec 32 := v.extractLsb' 32 32

def low32 (v : BitVec 64) : BitVec 32 := v.extractLsb' 0 32

@[simp] theorem high32_pack (hi lo : BitVec 32) : high32 (pack hi lo) = hi :=
  BitVec.extractLsb'_append_eq_left

@[simp] theorem low32_pack (hi lo : BitVec 32) : low32 (pack hi lo) = lo :=
  BitVec.extractLsb'_append_eq_right

@[simp] theorem high32_zero : high32 0#64 = 0#32 := by decide +kernel

@[simp] theorem low32_zero : low32 0#64 = 0#32 := by decide +kernel

theorem pack_xor (hi lo hi' lo' : BitVec 32) :
    pack hi lo ^^^ pack hi' lo' = pack (hi ^^^ hi') (lo ^^^ lo') :=
  BitVec.xor_append

theorem pack_high32_low32 (v : BitVec 64) : pack (high32 v) (low32 v) = v :=
  BitVec.extractLsb'_append_extractLsb'

theorem pack_eq_shift_or (hi lo : BitVec 32) :
    pack hi lo = ((hi.zeroExtend 64 <<< (32 : Nat)) ||| lo.zeroExtend 64) := by
  simpa only [pack, BitVec.zeroExtend_eq_setWidth, BitVec.setWidth_eq] using
    (BitVec.setWidth_append_eq_shiftLeft_setWidth_or (b := hi) (b' := lo) (w'' := 64))

private def m₁ : BitVec 64 := 0xff51afd7ed558ccd
private def m₂ : BitVec 64 := 0xc4ceb9fe1a85ec53
private def inv₁ : BitVec 64 := 0x4f74430c22a54005
private def inv₂ : BitVec 64 := 0x9cb4b2f8129337db

private theorem m₁_inv₁ : m₁ * inv₁ = 1#64 := by decide +kernel
private theorem m₂_inv₂ : m₂ * inv₂ = 1#64 := by decide +kernel

def xorShift33 (v : BitVec 64) : BitVec 64 := v ^^^ (v >>> (33 : Nat))

@[simp] theorem xorShift33_twice (v : BitVec 64) : xorShift33 (xorShift33 v) = v := by
  unfold xorShift33
  rw [BitVec.ushiftRight_xor_distrib, ← BitVec.shiftRight_add]
  rw [BitVec.ushiftRight_eq_zero (by decide : 64 ≤ 33 + 33)]
  simp [BitVec.xor_assoc]

def mix64 (v : BitVec 64) : BitVec 64 :=
  xorShift33 (xorShift33 (v * m₁) * m₂)

def unmix64 (v : BitVec 64) : BitVec 64 :=
  xorShift33 (xorShift33 v * inv₂) * inv₁

@[simp] theorem unmix64_mix64 (v : BitVec 64) : unmix64 (mix64 v) = v := by
  simp only [mix64, unmix64, xorShift33_twice, BitVec.mul_assoc, m₁_inv₁, m₂_inv₂,
    BitVec.mul_one]

@[simp] theorem mix64_unmix64 (v : BitVec 64) : mix64 (unmix64 v) = v := by
  have inv₁_m₁ := (BitVec.mul_comm inv₁ m₁).trans m₁_inv₁
  have inv₂_m₂ := (BitVec.mul_comm inv₂ m₂).trans m₂_inv₂
  simp only [mix64, unmix64, xorShift33_twice, BitVec.mul_assoc, inv₁_m₁, inv₂_m₂,
    BitVec.mul_one]

/-- The C verifier assigns the unsigned 32-bit input to a 64-bit word. -/
def H (x : BitVec 32) : BitVec 64 := mix64 (x.zeroExtend 64)

@[simp] theorem H_zero : H 0#32 = 0#64 := by decide +kernel

theorem zeroExtend_eq_pack (x : BitVec 32) : x.zeroExtend 64 = pack (0#32) x := by
  simpa only [BitVec.zeroExtend_eq_setWidth, pack, BitVec.cast_eq] using
    (BitVec.setWidth_eq_append (x := x) (w := 64) (by decide : 32 ≤ 64))

@[simp] theorem unmix64_H (x : BitVec 32) : unmix64 (H x) = pack (0#32) x := by
  rw [H, unmix64_mix64, zeroExtend_eq_pack]

theorem H_injective {x y : BitVec 32} (h : H x = H y) : x = y := by
  simpa using congrArg (fun v => low32 (unmix64 v)) h

/-- The result of C's `inverse_H`: success with the recovered word, or failure. -/
def inverseH (v : BitVec 64) : Option (BitVec 32) :=
  let x := unmix64 v
  if high32 x = 0#32 then some (low32 x) else none

theorem high32_eq_zero_iff_shift (v : BitVec 64) :
    high32 v = 0#32 ↔ v >>> (32 : Nat) = 0#64 := by
  have hfit : (v >>> (32 : Nat)).toNat < 2^32 :=
    BitVec.toNat_ushiftRight_lt v 32 (by decide)
  rw [BitVec.toNat_eq, high32, BitVec.extractLsb'_toNat, ← BitVec.toNat_ushiftRight,
    Nat.mod_eq_of_lt hfit, BitVec.toNat_eq]
  rfl

/-- The bit-vector operations corresponding to C's shift test and unsigned cast. -/
theorem inverseH_eq_shift_and_truncate (v : BitVec 64) :
    inverseH v =
      (let x := unmix64 v
       if x >>> (32 : Nat) = 0#64 then some (x.setWidth 32) else none) := by
  simp only [inverseH, high32_eq_zero_iff_shift, low32,
    BitVec.setWidth_eq_extractLsb' (by decide : 32 ≤ 64)]

theorem inverseH_eq_some_iff (v : BitVec 64) (x : BitVec 32) :
    inverseH v = some x ↔ H x = v := by
  constructor
  · intro h
    dsimp only [inverseH] at h
    split at h
    next hhi =>
      have hlo : low32 (unmix64 v) = x := Option.some.inj h
      have hunmix : unmix64 v = pack (0#32) x := by
        rw [← pack_high32_low32 (unmix64 v), hhi, hlo]
      rw [H, zeroExtend_eq_pack, ← hunmix, mix64_unmix64]
    next => contradiction
  · rintro rfl
    simp [inverseH]

theorem inverseH_eq_none_iff (v : BitVec 64) :
    inverseH v = none ↔ high32 (unmix64 v) ≠ 0#32 := by
  by_cases h : high32 (unmix64 v) = 0#32 <;> simp [inverseH, h]

/-- Phase 1 of the C verifier, proved for every unsigned 32-bit input. -/
theorem inverseH_H (x : BitVec 32) : inverseH (H x) = some x :=
  (inverseH_eq_some_iff (H x) x).2 rfl

theorem mem_image_H_iff (v : BitVec 64) :
    (∃ x : BitVec 32, H x = v) ↔ high32 (unmix64 v) = 0#32 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · intro h
    exact ⟨low32 (unmix64 v), (inverseH_eq_some_iff _ _).1 (by simp [inverseH, h])⟩

end HashProof
