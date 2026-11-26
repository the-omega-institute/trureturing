import GRH.Lib.Shimura.AbelianScheme.Specialisation
import GRH.Lib.Shimura.ThetaGroup.SectionLifts
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Theta group of an ample line bundle: span of sections, K(L), symmetric theta structures
(known result; see Lib.Shimura.ThetaGroup.RigidFibres).

This file: Symmetric theta coordinates are unique; K(L) is killed by the order of the index set. -/

open AddChar AlgebraicGeometry CategoryTheory Fint Set Submodule Over

attribute [local simp] IsTranslationLift smul_smul

variable {R} [CommRing R] {A : Over (Spec ⟨R⟩)} {ι} {L :
  LineBundle A.1 ι} [AddObj A] {z Φ} {H : Type} [AddCommGroup H]

lemma IsTranslationLift.mul {w Ψ} (h : IsTranslationLift L z Φ) (h' : IsTranslationLift L w Ψ) :
  IsTranslationLift L (z + w) (Φ * Ψ) := by simpa [← comp_left, add_assoc] using! h.comp h'

lemma IsTranslationLift.pow (h : IsTranslationLift L z Φ) k : IsTranslationLift L (k • z) (Φ ^ k) :=
  k.rec (by simp; apply isSectionLift_pullSections <;> simp) (succ_nsmul z · ▸ ·.mul h)

lemma exists_isTranslationLift_iff [IsLocalRing R] :
    (∃ Φ, IsTranslationLift L z Φ) ↔ L.picClass.pairing
  (SemiCartesianMonoidalCategory.toUnit A ≫ z) (𝟙 A) = 0 := .trans ⟨(·.choose_spec.picClass_eq),
  exists_isSectionLift _⟩ (by simpa [Pic.pairing, add_comm] using! comm)

/-- A theta structure on N: coordinates X_t (t ∈ H, |H| invertible), each x ↦ ±x + η(s) lifting
to X_t ↦ c(s,t)X_{±(s+t)}, with c(s,−t) = c(t,s); X_s = X_0 on Lg, ∑_{l∈Lg} c(s,l)² = 0 off
Lg. -/
structure IsThetaStructure (Lg : AddSubgroup H) (η : H →+ (_ ⟶ A)) {N} hN (c : H →
  AddChar H R) where
  neg_eq_swap s t : c s (-t) = c t s
  theta_law (m : ℤˣ) s : ∃ Φ : Module.End R _, IsSectionLift N N ((m.1 • 𝟙 A) ≫ translation
    (η s)).left Φ ∧ ∀ t, Φ (coordSection hN t) = c s t • coordSection hN (m.1 • (s + t))
  coordSection_eq_of_mem : ∀ s ∈ Lg, coordSection hN s = coordSection hN 0
  isUnit_card : IsUnit (Nat.card H : R)
  sum_sq_eq_zero [Fintype Lg] : ∀ s ∉ Lg, ∑ l : Lg, c s l ^ 2 = 0

variable {Lg η} {N : LineBundle A.left H} {hN : N.IsLinearSystem} {c} (h :
  IsThetaStructure Lg η hN c) [Finite H] (r : HasConstFunctions A.hom ∧
  span R (range (coordSection hN)) = ⊤) {A'} [AddObj A'] {η'} {N' : LineBundle A'.left H}
  {hN' : N'.IsLinearSystem} {c' : H → AddChar H R} (h' : IsThetaStructure Lg η' hN' c')

include h r h'

lemma IsThetaStructure.pull_eq_of_intertwines {f T} {U : H → Module.End R _} (e : ∀ s t,
  U s (coordSection hN t) = c s t • coordSection hN (s + t)) (hT : IsSectionLift N _ f T) (hy : ∀ s,
  T (coordSection hN' s) = U s (T (coordSection hN' 0))) : N'.pull f = N := (mem_span_singleton.1
  ((smul_mem_iff_of_isUnit _ (isUnit_of_dvd_unit Lg.card_addSubgroup_dvd_card.natCast h.4)).1
  (by simpa [← hy, h'.3, Nat.cast_smul_eq_nsmul] using ((R ∙ coordSection hN 0).map_span_le (∑ l :
  Lg, U (-l)) _).2 (forall_mem_range.2 fun t ↦ by by_cases t ∈ Lg <;> simp [*, ← sq, h.3, h.5, fun l
  k ↦ by simpa [e, ← map_add_eq_mul] using (congr(c t (-l) • U t $(h.3 l k))), ← h.1 t, add_comm,
  ← Finset.sum_smul, nsmul_mem]) ⟨T (coordSection hN' 0), r.2.ge ⟨⟩, rfl⟩))).elim fun a ha ↦
  hT.pull_eq_of_coordSection _ _ (by simpa [← ha, e] using hy)

/-- Rigidity: let N, N' be theta structures on A, A' for the same Lg, |H| odd, functions on A
constant, H⁰(N) spanned by coordinates. A homomorphism f carrying η to η' with [N] = f^*[N'] has
f^*N' = N.

Known result: Theta group of an ample line bundle: span of sections, K(L), symmetric theta
structures. -/
lemma IsThetaStructure.pull_eq_of_picClass_eq (ho : Odd (Nat.card H)) f [IsAdditive f] (hη : ∀ s,
  η s ≫ f = η' s) (e : N.picClass = N'.picClass.pull f.left) : N'.pull f.left = N :=
  (exists_isSectionLift f e).elim fun T hT ↦ by
  choose U hU eU using h.theta_law
  choose U' hU' _ using h'.theta_law
  choose b _ using fun m s ↦ (hT.comp (hU' m s)).exists_eq_smul r.1 (by
    simpa [← comp_left, *] using (hU ..).comp hT)
  have K s : U 1 (s + s) * U (-1) 0 * U 1 s = U 1 s * U (-1) 0 := LinearMap.ext_on_range r.2 (by
    simp [eU]; grind only [IsThetaStructure, map_add_eq_mul, add_neg_cancel])
  exact h.pull_eq_of_intertwines r h' (by simpa using eU 1) hT
    (ho.coprime_two_right.nsmul_right_bijective.2.forall.2 fun s ↦ by simpa [*, h'.1, two_smul,
    (val_isUnit ..).smul_left_cancel] using (by simp_all [DFunLike.ext_iff, mul_comm] :
    ∀ v, T (U' 1 s (U' (-1) 0 v)) = U 1 (s + s) (T (U' (-1) 0 (U' 1 s v)))) (coordSection hN' (-s)))

omit h'

/-- Over a ring R, let global functions on A be constant and (N, c) a theta structure indexed by
finite H, with N a projective embedding whose coordinates span H⁰(N). Then |H| kills every section y
whose translation lifts to N (via Ψ); over a local ring R these are exactly the sections y in the
kernel K([N]). -/
lemma IsThetaStructure.card_nsmul_eq_zero_of_lift (hE : N.IsProjEmbedding A.hom) {y Ψ} (P :
  IsTranslationLift N y Ψ) : Nat.card H • y = 0 := by
  choose U hU eU using by simpa using h.theta_law 1
  simpa using y ≫= OverMorphism.ext (g := 𝟙 A) (hE.ext
    (h.pull_eq_of_intertwines r h eU (P.pow _) fun s ↦ P.injective (((P.pow _).exists_eq_smul r.1
    (by simpa [← map_nsmul] using (P.mul (hU s)).pow (Nat.card H))).elim fun a e ↦ by
    simpa [eU, ← LinearMap.ext (g := a • _) e, pow_mul_comm', ← mul_assoc] using
      congr($((Commute.pow_self (Ψ * U s) (Nat.card H)).smul_left a) (coordSection _ 0)))) (w _))
