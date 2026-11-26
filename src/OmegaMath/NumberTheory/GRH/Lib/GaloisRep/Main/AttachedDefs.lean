import OmegaMath.NumberTheory.GRH.Lib.GaloisRep.Main.LocalEmbedding
import OmegaMath.NumberTheory.GRH.Lib.ClassField.Chebotarev.FrobeniusFilter
import OmegaMath.NumberTheory.GRH.Lib.GaloisRep.LocalGlobal.LocalTranslates
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Galois representations attached to forms on definite unitary groups (known result; see
Lib.GaloisRep.Main.AvatarCompatibility).

This file: Definition of attached representation and statement of the main theorem. -/


variable {ℓ : ℕ} [ThePrime ℓ] [PadicIso ℓ] {E : Type} {n} [Field E] [NumberField E] [Algebra E Ω]
  [Fintype n] [NumberField.IsCMField E] (P : FinPlace E → _)

/-- ρ is continuous and semisimple, j is open, and for each η > 0, most Frobenii s at w have
det(X − ρ(x)) coefficientwise within η of ιP_w whenever j(x) = s. -/
def Attached {H} [Group H] [TopologicalSpace H] (ρ : H →* GL n (PadicAlgCl ℓ)) (j : H → Gal(Ω/E) :=
    by exact id) := Continuous ρ ∧ IsTraceNondeg ρ ∧ IsOpenMap j ∧ ∀ η > 0, ∀ᶠ y in mostFrobenii E,
  ∀ x, j x = y.frob → ∀ i, ‖((ρ x).1.charpoly - .map ιℓ.toRingHom (P y.w)).coeff i‖ ≤ η

variable (E n) in
variable (E : Type) (n : _) [Field E] [CMType E] [Algebra E Ω] [Fintype n] in
/-- Every eigenform f on the standard space has an attached r; if K_w fixes f, every attached r is
unramified or crystalline at w, with the jumps of κ in rank N, and ιQ kills geometric Frobenius when
f has Hecke polynomial Q at w. -/
def SphericalCompat N w := ∀ ⦃P κ f⦄, f ∈ (stdSpace ..).forms κ → IsEigenform f P →
  (∃ r : GalRep ℓ E n, Attached P r) ∧ ∀ ⦃r : GalRep ℓ E n⦄, Attached P r → f ∈ levelSpace
  (rightRegular ℂ ..) (maxCompactAt n w) 1 → ∀ A, IsPlaceOver A w → IsGoodAt r A ∧
  HasJumpsAt r A (jumps κ N) ∧ ∀ hw Q,
  HasHeckePolyAt f w hw Q → ∀ s, IsFrob A w.q s⁻¹ → PolyKillsAt r A s (Q.map ιℓ.toRingHom)

lemma isRoot_of_isRoot_charpoly {K} [Field K] {M : Matrix n n K} {P x} (h : Polynomial.aeval M P =
  0) : M.charpoly.IsRoot x → P.IsRoot x := (by aesop) ∘ (·.dvd (charpoly_dvd_charpoly_aeval_comp P))
