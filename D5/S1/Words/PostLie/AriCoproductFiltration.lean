/- GID: D5/S1/Words/PostLie/AriCoproductFiltration
   generality: I
   mirror-B: D5/B/S1/Words/PostLie/AriCoproductFiltration
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The finite ordinary ari transpose preserves every right-factor level filtration. -/


import D5.S1.Words.PostLie.AriWordProduct

/-! Finite weight windows, the ordinary tensor transpose, and the full filtration assertion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S1.Words.PostLie.AriCoproductFiltration

open scoped BigOperators TensorProduct
open D5.S1.Words.PostLie.AriWordOperations
open D5.S1.Words.PostLie.AriWordProduct

/-- The ordinary rational tensor-word basis, with no factorial normalization. -/
def tensorBasis : Module.Basis (Word × Word) ℚ (H ⊗[ℚ] H) :=
  wordBasis.tensorProduct wordBasis

private theorem length_le_weight (w : List ℕ) : w.length ≤ weight (FreeMonoid.ofList w) := by
  induction w with
  | nil => simp
  | cons a w ih =>
    have hg : 1 ≤ gamma a := by unfold gamma; split_ifs <;> omega
    simp only [weight, FreeMonoid.toList_ofList, List.map_cons, List.sum_cons, List.length_cons] at *
    omega

private theorem index_le_weight (w : List ℕ) (a : ℕ) (ha : a ∈ w) :
    a ≤ weight (FreeMonoid.ofList w) := by
  induction w with
  | nil => simp at ha
  | cons b w ih =>
    have hg : b ≤ gamma b := by unfold gamma; split_ifs <;> omega
    simp only [List.mem_cons] at ha
    simp only [weight, FreeMonoid.toList_ofList, List.map_cons, List.sum_cons]
    rcases ha with rfl | ha
    · omega
    · have := ih ha
      dsimp [weight] at this
      omega

/-- Exactly all words of original weight at most `N`, obtained from bounded lists
on the genuine finite alphabet `Fin (N+1)`. -/
def weightWindow (N : ℕ) : Finset Word := by
  classical
  exact ((List.finite_length_le (Fin (N + 1)) N).toFinset.image
    (fun l => FreeMonoid.ofList (l.map Fin.val))).filter (fun w => weight w ≤ N)

theorem mem_weightWindow (N : ℕ) (w : Word) : w ∈ weightWindow N ↔ weight w ≤ N := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro hw
    apply Finset.mem_filter.mpr
    refine ⟨?_, hw⟩
    let l : List (Fin (N + 1)) := w.toList.attach.map fun a =>
      ⟨a.1, Nat.lt_succ_of_le ((index_le_weight w.toList a.1 a.2).trans hw)⟩
    apply Finset.mem_image.mpr
    refine ⟨l, ?_, ?_⟩
    · apply (List.finite_length_le (Fin (N + 1)) N).mem_toFinset.mpr
      change l.length ≤ N
      simpa [l] using (length_le_weight w.toList).trans hw
    · apply FreeMonoid.toList.injective
      simp [l, List.map_map]

private theorem transpose_support (w : Word) (ab : Word × Word)
    (h : (starWord ab.1 ab.2).coeff w ≠ 0) :
    ab ∈ (weightWindow (weight w)) ×ˢ (weightWindow (weight w)) := by
  have he := starWord_homogeneous ab.1 ab.2 w h
  change weight w = weight ab.1 + weight ab.2 at he
  apply Finset.mem_product.mpr
  constructor <;> apply (mem_weightWindow _ _).mpr <;> omega

/-- The finite transpose on a basis word. `onFinset` carries exactly the ordinary
product coefficients and proves their support lies in a finite weight window. -/
def deltaWord (w : Word) : H ⊗[ℚ] H :=
  tensorBasis.repr.symm (Finsupp.onFinset
    ((weightWindow (weight w)) ×ˢ (weightWindow (weight w)))
    (fun ab => (starWord ab.1 ab.2).coeff w) (transpose_support w))

/-- Ordinary word pairing, as a bilinear map on finite rational polynomials. -/
def pairing : H →ₗ[ℚ] H →ₗ[ℚ] ℚ :=
  wordBasis.constr ℚ fun A =>
    (Finsupp.lapply A).comp (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap

private theorem pairing_basis (w : Word) (P : H) : pairing (wordBasis w) P = P.coeff w := by
  simp [pairing]

/-- The ordinary transpose characterization from Definition 1.20 and Remark 1.22,
using the original primitive-unshuffle product and every pair of word coordinates. -/
def transposeProperty (D : H →ₗ[ℚ] H ⊗[ℚ] H) : Prop :=
  ∀ (P : H) (A B : Word),
    tensorBasis.repr (D P) (A, B) = pairing P (star (wordBasis A) (wordBasis B))

private def finiteTranspose : H →ₗ[ℚ] H ⊗[ℚ] H := wordBasis.constr ℚ deltaWord

private theorem finiteTranspose_basis_coefficient (w A B : Word) :
    tensorBasis.repr (finiteTranspose (wordBasis w)) (A, B) = (starWord A B).coeff w := by
  simp [finiteTranspose, deltaWord]

private theorem finiteTranspose_property : transposeProperty finiteTranspose := by
  intro P A B
  rw [star_basis]
  have he : (Finsupp.lapply (A, B)).comp (tensorBasis.repr.toLinearMap.comp finiteTranspose) =
      (LinearMap.applyₗ (starWord A B)).comp pairing := by
    apply wordBasis.ext
    intro w
    simpa [pairing_basis] using finiteTranspose_basis_coefficient w A B
  exact LinearMap.congr_fun he P

private theorem exists_unique_transpose : ∃! D, transposeProperty D := by
  refine ⟨finiteTranspose, finiteTranspose_property, ?_⟩
  intro D hD
  apply wordBasis.ext
  intro w
  apply tensorBasis.repr.injective
  ext ab
  exact (hD (wordBasis w) ab.1 ab.2).trans
    (finiteTranspose_property (wordBasis w) ab.1 ab.2).symm

/-- The original ordinary ari coproduct: the unique linear transpose of `star`.
Its existence in the algebraic tensor product is proved by the finite weight-window
construction, without a completion or an assumed realization map. -/
def delta : H →ₗ[ℚ] H ⊗[ℚ] H := Classical.choose exists_unique_transpose.exists

/-- The defining ordinary transpose identity for arbitrary rational input and all
word pairs, with the actual primitive-unshuffle product. -/
theorem delta_coefficient (P : H) (A B : Word) :
    tensorBasis.repr (delta P) (A, B) = pairing P (star (wordBasis A) (wordBasis B)) :=
  Classical.choose_spec exists_unique_transpose.exists P A B

/-- Full ordinary basis coefficients, including pairs outside the finite window
and either unit word; there is no factorial normalization. -/
theorem delta_basis_coefficient (w A B : Word) :
    tensorBasis.repr (delta (wordBasis w)) (A, B) = (starWord A B).coeff w := by
  rw [delta_coefficient, star_basis, pairing_basis]

/-- The original increasing `k`-level filtration, as the actual rational span. -/
def filtration (k r : ℕ) : Submodule ℚ H :=
  Submodule.span ℚ (wordBasis '' {w | level k w ≤ r})

/-- The image of `H tensor filtration` under its natural inclusion in `H tensor H`. -/
def rightFiltrationImage (k r : ℕ) : Submodule ℚ (H ⊗[ℚ] H) :=
  LinearMap.range (TensorProduct.map (LinearMap.id : H →ₗ[ℚ] H) (filtration k r).subtype)

private theorem tensor_span_le_image (k r : ℕ) :
    Submodule.span ℚ (tensorBasis '' {ab | level k ab.2 ≤ r}) ≤ rightFiltrationImage k r := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨A, B⟩, hB, rfl⟩
  have hb : wordBasis B ∈ filtration k r :=
    Submodule.subset_span ⟨B, hB, rfl⟩
  refine ⟨wordBasis A ⊗ₜ[ℚ] (⟨wordBasis B, hb⟩ : filtration k r), ?_⟩
  simp [tensorBasis]

private theorem delta_basis_mem (k r : ℕ) (w : Word) (hw : level k w ≤ r) :
    delta (wordBasis w) ∈ rightFiltrationImage k r := by
  apply tensor_span_le_image k r
  apply tensorBasis.mem_span_image.mpr
  intro ab hab
  have hn : tensorBasis.repr (delta (wordBasis w)) ab ≠ 0 :=
    Finsupp.mem_support_iff.mp hab
  rw [delta_basis_coefficient w ab.1 ab.2] at hn
  exact (starWord_above k ab.1 ab.2 w hn).trans hw

/-- Complete original Burmester--Kühn Conjecture 4.29, for all natural `k,r`
and all finite rational word polynomials, including the unit. -/
def claim : Prop := ∀ (k r : ℕ) (P : H),
  P ∈ filtration k r → delta P ∈ rightFiltrationImage k r

/-- The full right-factor filtration assertion for the original finite transpose. -/
theorem result : claim := by
  intro k r P hP
  have hs : filtration k r ≤ (rightFiltrationImage k r).comap delta := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    exact delta_basis_mem k r w hw
  exact hs hP

end D5.S1.Words.PostLie.AriCoproductFiltration
