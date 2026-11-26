import OmegaMath.NumberTheory.GRH.Lib.Shimura.IntegralModel.GroupBaseChange
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! General lemmas of algebraic geometry (textbook or folklore).

Part of: Abelian schemes: isogenies finite flat, [m]*L = L^{m²}, Cartier, unramified torsion (known
result; see Lib.Shimura.AbelianScheme.ThetaFamily).

This file: Lie algebra via étale charts and square-zero extensions; action matrices; signature
condition. -/

noncomputable section

open CategoryTheory AlgebraicGeometry TrivSqZeroExt CommRingCat Spec Over Matrix IsLocalRing


variable {S X : Scheme} {A : Over S} {ι O R M : Type} {B C C' D : CommRingCat} {V} (f : X ⟶ S)
  [AddObj A] {t : Spec C ⟶ S} {s : Spec B ⟶ S} (ψ : C ⟶ C') (z : ι → Γ(A.1, V)) (y : .mk t ⟶ A)
  [CommRing O] [ModuleObj O A] [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ
  M] [IsCentralScalar R M]

lemma exists_isAffineOpen_landsIn [IsLocalRing B] (t : Spec B ⟶ X) : ∃ V, IsAffineOpen V ∧
  LandsIn t V := by simpa [landsIn_iff_mem] using @exists_isAffineOpen_mem_and_subset _ _ ⊤ ⟨⟩

/-- The ring homomorphism ψ is surjective and its kernel has square zero. -/
class IsSqZeroExt where surjective_and_mul_eq_zero : (⇑ψ).Surjective ∧ ∀ a b, ψ a = 0 → ψ b = 0 →
  a * b = 0

/-- For ψ : C → C', the C-point y of the group scheme A becomes 0 in A(C'). -/
def IsInfinitesimal := (homMk _ : mk (map ψ ≫ t) ⟶ _) ≫ y = 0

/-- For a C-point y of A, the vector of differences z_i(y) − z_i(0) in C of the values of the
functions z_i at y and at the zero point. -/
def tangentCoords i := PointFn.ofSection (z i) C y.1 - PointFn.ofSection (z i) C (0 : mk t ⟶ A).1

/-- The z_i are regular on V and étale coordinates for f: along square-zero extensions C → C',
points in V lift uniquely over S with any prescribed lifts of the values z_i. -/
def IsEtaleChart V (z : ι → Γ(X, V)) := ∀ ⦃C D ψ⦄ [@IsSqZeroExt C D ψ] ⦃t⦄ x l, LandsIn x V →
  x ≫ f = map ψ ≫ t → ψ ∘ l = (PointFn.ofSection · _ x) ∘ z → ∃! y : mk t ⟶ mk f, map ψ ≫ y.1 = x ∧
  (PointFn.ofSection · C y.1) ∘ z = l

variable (R M) in
abbrev sqZeroReduction := specMap (fstHom R R M).1

instance isSqZeroExt_fstHom : IsSqZeroExt (ofHom (fstHom R R M).1) := ⟨fst_surjective, by aesop⟩

variable (A) in
/-- The functions z are coordinates at 0 over s where O acts by matrices m. -/
def IsLieChart [Fintype ι]
    s V z (m : O → Matrix ι ι B) := IsEtaleChart A.hom V z ∧ ∀ ⦃C φ t⦄, map φ ≫ s = t →
  LandsIn (0 : mk t ⟶ A).left V ∧ ∀ ⦃D ψ⦄ [@IsSqZeroExt C D ψ] ⦃y : mk t ⟶ A⦄, IsInfinitesimal ψ y →
  (∀ a, tangentCoords z (a • y) = (m a).map φ *ᵥ tangentCoords z y) ∧ ∀ x, IsInfinitesimal ψ x →
  tangentCoords z (y + x) = tangentCoords z y + tangentCoords z x

/-- Some vector X with a unit coordinate has m(a)X = ρ(a)X for all a in O, and m(b) − ρ(b')·1 =
Xξᵀ for some vector ξ. -/
def HasSignature [Fintype ι] (ρ : O →+* R) b b' (m : O → Matrix ι ι R) := ∃ X ξ k,
  IsUnit (X k) ∧ (∀ a, m a *ᵥ X = ρ a • X) ∧ m b - ρ b' • 1 = vecMulVec X ξ

variable {ψ z f y}
attribute [local simp] dotProduct funext_iff sq

lemma IsSqZeroExt.surjective (h : IsSqZeroExt ψ) : Surjective (map ψ) :=
  ⟨(PrimeSpectrum.isHomeomorph_comap _
  (⟨1, by simp [h.1.1 ·]⟩) fun _ _ ↦ ⟨2, by simp_all [h.1]⟩).3.2⟩

lemma IsSqZeroExt.landsIn_of_comp (h : IsSqZeroExt ψ) {y V} : @LandsIn X _ (map ψ ≫ y) V →
  LandsIn y V := (h.surjective.1.forall.2 ·)

open MvPolynomial Algebra FormallySmooth FormallyUnramified RingHom in
/-- If f : X → S is smooth of relative dimension d, every point x of X has an open neighbourhood
V on which some d functions are étale coordinates for f. -/
lemma exists_isEtaleChart x {d} (H : SmoothOfRelativeDimension d f) : ∃ V, ∃ z : Fin d → _, x ∈ V ∧
    IsEtaleChart f V z := have ⟨U, hU, V, hV, hx, e, H⟩ := H.1 x
  H.exists_etale_mvPolynomial.rec fun g ⟨hg, H⟩ ↦ ⟨V, g ∘ .X, hx, fun C C' ψ h t x l i w k ↦ by
    have K {C ρ σ l} := (by simp [-map_comp, map_inj, hg, ← hU.SpecMap_appLE_fromSpec _ hV e,
      ← map_comp_assoc, cancel_mono, CommRingCat.hom_ext_iff, comp_assoc,
      MvPolynomial.ringHom_ext'_iff] : let y := map ρ ≫ hV.fromSpec; y ≫ f = map σ ≫ hU.fromSpec
      ∧ (PointFn.ofSection · C y) ∘ g ∘ .X = l ↔ ρ.hom.comp g =
        eval₂Hom σ.hom l).trans RingHom.ext_iff
    obtain ⟨⟨σ, rfl⟩, ξ, rfl⟩ := landsIn_opensRange.1 (hU.opensRange_fromSpec ▸ h.landsIn_of_comp
      (w ▸ landsIn_preimage.1 (i.mono e))), landsIn_opensRange.1 (hV.opensRange_fromSpec ▸ i)
    algebraize [g, eval₂Hom σ.1 l, eval₂Hom (σ ≫ ψ).1 (ψ ∘ l)]
    have n : IsNilpotent (ker ψ.hom) := ⟨2, by simp_all [h.1, ← le_bot_iff, Ideal.mul_le]⟩
    obtain ⟨ρ, rfl⟩ : ∃ ρ : AlgHom .., ofHom ρ.1 ≫ ψ = ξ := ⟨_, congr(ofHom $(comp_liftOfSurjective
      ⟨ξ.1, K.1 (by simp [*])⟩ ⟨ψ.1, map_eval₂Hom _ _ _⟩ h.1.1 n).1)⟩
    refine ((K (ρ := ofHom ρ)).2 ρ.2).rec (⟨homMk _ ·, ⟨by simp, ·⟩, fun ⟨y, _, a⟩ ⟨b, c⟩ ↦ ?_⟩)
    obtain ⟨ρ', rfl⟩ := landsIn_opensRange.1 (h.landsIn_of_comp (landsIn_opensRange.2 ⟨_, b.symm⟩))
    exact ext' _ n ⟨ρ'.1, K.1 ⟨a, c⟩⟩
      ρ (by simpa [← map_comp_assoc, -map_comp] using! congr(PointFn.ofSection · _ $b)) ▸ rfl⟩

@[simp] lemma tangentCoords_zero : tangentCoords z (0 : mk t ⟶ A) = 0 := sub_self _

/-- Let σ_n : B → D be ring maps with jointly trivial kernel such that the rank-one condition
`HasSignature` holds after each σ_n. Then it holds after every φ : B → C with C local and
φ(ρ(b) − ρ(b')) a unit. -/
lemma HasSignature.of_points [Fintype ι]
    {ρ : O →+* B} {b b' N} {m : O → Matrix ι ι B} {σ : N → (B ⟶ D)} (h :
  ∀ r, (∀ n, σ n r = 0) → r = 0) (H : ∀ n, HasSignature ((σ n).hom.comp ρ) b b' (m · |>.map (σ n)))
  (φ : B ⟶ C) [IsLocalRing C] (u : IsUnit (φ (ρ b - ρ b'))) :
  HasSignature (φ.hom.comp ρ) b b' (m · |>.map φ) := by
  choose X ξ k v e f using H
  obtain ⟨⟨q, Q⟩, _⟩ := add_left_surjective (ρ b' • 1) (m b), (e · b)
  simp [HasSignature, ← Q, Matrix.map_add, map_smul', entrywise, vecMulVec, -map_sub] at *
  rw [sub_eq_zero.1 (h (_ - _ - ∑ k, q k k) (v · |>.mul_left_eq_zero.1 (by
    simp [sub_mul, Finset.sum_mul]; grind))), map_sum] at u
  exact (exists_of_isUnit_sum u).rec fun k ⟨_, c, u⟩ ↦ ⟨_, ⟨k, c, u⟩, fun a i ↦ by simpa using (
    congrArg φ (h (_ ⬝ᵥ qᵀ k - _ * _) (by simp_all [← mul_assoc, ← Finset.sum_mul]))), (c.2 *
    φ ·) ∘ q k, fun i j ↦ by grind [congrArg φ (h (q k k * q i j - q i k * q k j) (by grind)), c.3]⟩

variable (hz : IsEtaleChart A.hom V z) (i : LandsIn (0 : mk t ⟶ A).left V) (hy :
  IsInfinitesimal ψ y) {χ}
include hy

lemma IsInfinitesimal.smul (c : O) : IsInfinitesimal ψ (c • y) := by simp_all [IsInfinitesimal]

variable {t' : Spec D ⟶ S} (a : mk t' ⟶ mk t) (e : a.left = Spec.map χ) [h : IsSqZeroExt ψ]

include e in
omit [IsSqZeroExt ψ] in
lemma IsInfinitesimal.precomp {φ : D ⟶ B} κ (w : χ ≫ φ = ψ ≫ κ) : IsInfinitesimal φ (a ≫ y) := by
  ext; simpa [*, Hom.zero_def, ← dsimp% a.w, ← map_comp_assoc, -map_comp] using congr(map κ ≫ $hy.1)

namespace IsEtaleChart

include hz i

omit hy h in
lemma existsUnique_tangentCoords_eq (h : IsSqZeroExt ψ) l (e : ∀ k, ψ (l k) = 0) : ∃! y : mk t ⟶ A,
  IsInfinitesimal ψ y ∧ tangentCoords z y = l :=
  (existsUnique_congr fun _ ↦ by exact OverMorphism.ext_iff.and sub_eq_iff_eq_add).2
  (hz _ _ (i.comp _) (by simp) (by simp [PointFn.isRegularOn_ofSection _ ψ, *]))

include e in
lemma tangentCoords_comp : tangentCoords z (a ≫ y) =
  χ ∘ tangentCoords z y := have _ := hz; by simp [← comp_zero a, -comp_zero, tangentCoords,
  PointFn.isRegularOn_ofSection _ χ, h.landsIn_of_comp (congr(LandsIn $hy.1 V).ge (i.comp _)), *]

lemma map_tangentCoords_eq_zero k : ψ (tangentCoords z y k) = 0 :=
  congrFun ((hy ▸ hz.tangentCoords_comp i hy _ rfl) ▸ tangentCoords_zero) k

lemma eq_zero_of_tangentCoords : tangentCoords z y = 0 → y = 0 :=
  ((hz.existsUnique_tangentCoords_eq i h 0 (by simp)).unique ⟨hy, ·⟩ ⟨rfl, tangentCoords_zero⟩)

end IsEtaleChart

omit hy in
/-- Coordinates at 0 exist (Taylor's formula to first order, in two variables). -/
lemma exists_isLieChart {g} (hd : SmoothOfRelativeDimension g A.hom) [IsLocalRing B] s : ∃ V z,
  ∃ m : O → Matrix (Fin g) _ B, ∀ {C t} {φ : B ⟶ C}, map φ ≫ s = t → IsLieChart A t V z (m · |>.map
  φ) := (exists_isEtaleChart ((0 : mk s ⟶ A).1 (closedPoint B)) hd).imp fun V ⟨z, i, hz⟩ ↦ by
  have i {C φ} : LandsIn (0 : mk (@map B C φ ≫ s) ⟶ A).1 V := (landsIn_iff_mem.2 i).comp _
  choose Y hY e using fun c ↦ (hz.existsUnique_tangentCoords_eq (@i _ (ofHom (inlHom B
    (Fin g ⊕ Fin g → B)))) isSqZeroExt_fstHom (inr ∘ (Pi.single · 1) ∘ c) (by simp)).exists
  let b (c : O) := snd ∘ tangentCoords z (c • (Y .inl + Y .inr))
  have H c {C C' φ ψ} [u : @IsSqZeroExt C C' ψ] {y : mk (map φ ≫ s) ⟶ A} y' (hy :
    IsInfinitesimal ψ y) (hy' : IsInfinitesimal ψ y') : tangentCoords z (c • (y + y')) =
    (φ ∘ b c · ⬝ᵥ (tangentCoords z y ⊕ᵥ tangentCoords z y')) := by
    set L := _ ⊕ᵥ _
    have N :=
      IsInfinitesimal.smul ((comp_add ..).trans ((add_eq_left.2 (hY .inr)).trans (hY .inl))) c
    have hl m : ψ (m ⬝ᵥ L) = 0 := by simp [L, hz.map_tangentCoords_eq_zero, *]
    algebraize [φ.1]
    let q :=
      (map s).2 (specOver.map (liftEquivOfComm ⟨Fintype.linearCombination B L, by bound [u.1]⟩))
    have E c {y} hy (k : tangentCoords z y = L ∘ c) := (hz.existsUnique_tangentCoords_eq i u
      (tangentCoords z y) (hz.map_tangentCoords_eq_zero i hy)).unique ⟨(hY c).precomp
      q rfl (φ ≫ ψ) (by ext; exact (map_add ..).trans (add_eq_left.2 (hl _))),
      by simp [hz.tangentCoords_comp i (hY c) q rfl, *]⟩ ⟨hy, rfl⟩
    simpa [b, E .inl hy rfl, E .inr hy' rfl, lift, -dotProduct,
      by simpa using hz.map_tangentCoords_eq_zero i N] using! hz.tangentCoords_comp i N q rfl
  use z, toCols₁ ∘ b, (· ▸ ⟨hz, fun _ _ _ ↦ (· ▸ map_comp_assoc .. ▸ ⟨i,
    fun _ _ _ _ hy ↦ ⟨(by simpa using! H · 0 hy rfl), fun _ hx ↦ by
    simpa using congr($(H 1 _ hy hx) - ($(H 1 0 hy rfl) + $(H 1 _ (comp_zero _) hx)))⟩⟩)⟩)

/-- Let A → S be smooth of constant relative dimension, Spec C → S factor through a local ring,
y ∈ A(C) vanish modulo a square-zero ideal, m ∈ ℕ. If m is invertible in C, my = 0 forces y
= 0; if m = 0 in C, my = 0. -/
lemma IsInfinitesimal.nsmul_injective_and_eq_zero {g} (hd :
  SmoothOfRelativeDimension g A.hom) [IsLocalRing B] (a : mk t ⟶ mk s)
  (m : ℕ) : (IsUnit (m : C) → m • y = 0 → y = 0) ∧ ((m : C) = 0 → m • y = 0) := by
  have ⟨_, z, _, J⟩ := exists_isLieChart hd s
  obtain ⟨_, _, J⟩ := (J (map_preimage a.left ▸ a.w)).imp_right (@· _ (𝟙 _) t (by simp))
  grind [(by induction m <;> simp [add_smul, @J _ ψ, *] <;> simp_all [IsInfinitesimal] :
    IsInfinitesimal ψ (m • y) ∧ tangentCoords z (m • y) = (m : C) • tangentCoords z y),
    IsEtaleChart.eq_zero_of_tangentCoords, IsUnit.smul_eq_zero, zero_smul]
