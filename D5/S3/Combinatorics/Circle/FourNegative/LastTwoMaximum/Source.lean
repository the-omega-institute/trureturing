/- GID: D5/S3/Combinatorics/Circle/FourNegative/LastTwoMaximum/Source
   generality: I
   mirror-B: none(waiver:private-consumed-source-dictionary)
   mirror-E: none(waiver:private-consumed-source-dictionary)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Literal tied-maximum source dictionary and exact selector definitions. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
namespace StrictDictionary
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers

private def x (a : ℕ) : ℤ := (2 : ℤ)^a
private def y (b : ℕ) : ℤ := (2 : ℤ)^b
private def z (s : ℕ) : ℤ := (2 : ℤ)^s
private def A (a b s : ℕ) : ℤ := 1 + x a + x a * y b + x a * y b * z s
private def B (a b s : ℕ) : ℤ := 1 + z s + x a * z s + x a * y b * z s
private def D (a b s : ℕ) : ℤ := B a b s - A a b s
private def L (a b s : ℕ) : ℤ := 1 + z s + z s ^ 2 + x a * z s ^ 2
private def K (a b s : ℕ) : ℤ := 1 + y b + y b * z s + y b * z s ^ 2
private def H (b s : ℕ) : ℤ := 1 + y b + y b * z s
private def SU (a b s : ℕ) : ℤ := 2 * B a b s - 1
private def SV (a b s : ℕ) : ℤ := 2 * L a b s - 1 - z s
private def SW (a b s : ℕ) : ℤ := 2 * K a b s - H b s
private def vNat (b : ℕ) : ℕ := 2^(b-2)
private def mask (s : ℕ) : ℕ := 2^(s-1)-1
private def hybridOld (a b s t : ℕ) : ℤ :=
  (t : ℤ) * B a b s - ((t % vNat b : ℕ) : ℤ) * D a b s
private def hybridNew (a b s t : ℕ) : ℤ :=
  2 * hybridOld a b s t - ((t - t % vNat b : ℕ) : ℤ)
private def quotientT (a b s : ℕ) : ℕ :=
  (L a b s - A a b s).toNat / (B a b s).toNat
private def wBit (a b : ℕ) : ℕ := 2^(b-a-1)

private theorem hybrid_decomposition (a b s t : ℕ) :
    hybridOld a b s t =
      ((t % vNat b : ℕ) : ℤ) * A a b s +
        ((t - t % vNat b : ℕ) : ℤ) * B a b s := by
  dsimp [hybridOld,D]
  have h : ((t - t % vNat b : ℕ) : ℤ) = (t : ℤ) - (t % vNat b : ℕ) :=
    Nat.cast_sub (Nat.mod_le _ _)
  rw [h]
  push_cast
  ring

private def vEndpoint (a b s t : ℕ) : ℤ :=
  L a b s - A a b s - hybridOld a b s t
private def vNewEndpoint (a b s t : ℕ) : ℤ :=
  2 * vEndpoint a b s t - (z s + 1) + (t - t % vNat b : ℕ)
private def wEndpoint (a b s u : ℕ) : ℤ :=
  K a b s - A a b s - hybridOld a b s u
private def wNewEndpoint (a b s u : ℕ) : ℤ :=
  2 * wEndpoint a b s u - H b s + (u - u % vNat b : ℕ)

private def borrowP (a s : ℕ) : ℕ := 2^(s-a-1)
private def borrowT (a b s : ℕ) : ℕ :=
  if s = a + 1 then
    if a = b + 1 then 2 else quotientT a b s - 1
  else
    let p := borrowP a s
    let t0 := quotientT a b s
    if Nat.testBit t0 (s-a-1) then t0 else t0-p
private def borrowU (a b s : ℕ) : ℕ := if s = a + 1 then 0 else borrowP a s

end StrictDictionary
end D5.S3.Combinatorics.Circle.FourNegative.LastTwoMaximum
