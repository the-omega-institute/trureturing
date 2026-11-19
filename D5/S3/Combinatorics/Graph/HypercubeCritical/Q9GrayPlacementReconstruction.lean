import D5.S3.Combinatorics.Graph.HypercubeCritical.CubicFiftyFourReconstruction
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementNormalForm

/-! Turn the reconstructed 54-vertex component into a placement by three
coordinate blocks and a center. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementReconstruction

open Finset
open Q9GrayPlacementNormalForm
open Q9TriplePartitionOrbits (standardLabels)
open BalancedCriticalSpectrum (IsBalanced)
open D5.S3.Combinatorics.Graph.Hypercube
attribute [local instance] Classical.propDecidable

private def allTrue : Vertex := fun _ => true

private theorem row_label : ∀ i : Fin 9,
    standardLabels i = (finProdFinEquiv.symm i : Fin 3 × Fin 3).1 := by
  decide +kernel

private theorem row_count (x : Vertex) (b : Fin 3) :
    (univ.filter (fun i => standardLabels i = b ∧ x i ≠ allTrue i)).card =
      (GrayGridComponent.falseRows x b).card := by
  symm
  apply card_bij (fun j _ => finProdFinEquiv (b, j))
  · intro j hj
    have hx : x (finProdFinEquiv (b, j)) = false := by
      simpa [GrayGridComponent.falseRows, GridWedgeComponent.gridRow] using hj
    exact mem_filter.mpr ⟨mem_univ _, by simp [row_label, allTrue, hx]⟩
  · intro i _ j _ h
    exact congrArg Prod.snd (finProdFinEquiv.injective h)
  · intro i hi
    have he : (finProdFinEquiv.symm i : Fin 3 × Fin 3).1 = b :=
      (row_label i).symm.trans (mem_filter.mp hi).2.1
    let j : Fin 3 := (finProdFinEquiv.symm i : Fin 3 × Fin 3).2
    have heq : finProdFinEquiv (b, j) = i := by
      rw [← he]
      exact finProdFinEquiv.apply_symm_apply i
    have hx := (mem_filter.mp hi).2.2
    refine ⟨j, ?_, heq⟩
    simp [GrayGridComponent.falseRows, GridWedgeComponent.gridRow, heq, allTrue] at hx ⊢
    exact hx

private theorem standard_support :
    GrayGridComponent.support 3 = placement standardLabels allTrue := by
  classical
  ext x
  let r (b : Fin 3) := (GrayGridComponent.falseRows x b).card
  have htotal : hammingDist x allTrue = ∑ b : Fin 3, r b := by
    classical
    change (univ.filter (fun i => x i ≠ allTrue i)).card = _
    have h := card_eq_sum_card_fiberwise (f := standardLabels)
      (s := univ.filter (fun i => x i ≠ allTrue i)) (t := univ) (by simp)
    simpa [filter_filter, and_comm, row_count, r] using h
  have hpoint : GrayGridComponent.pointPattern x ↔ ∀ b, r b = 1 := by
    simp [GrayGridComponent.pointPattern, r, card_eq_one]
  have hline : GrayGridComponent.linePattern x ↔
      ∃ b, r b = 0 ∧ ∀ c, c ≠ b → r c = 1 := by
    simp [GrayGridComponent.linePattern, GridWedgeComponent.singletonRowsOutside,
      GrayGridComponent.falseRows, r, card_eq_one, card_eq_zero]
  rw [GrayGridComponent.mem_support_iff, hpoint, hline, mem_placement]
  simp only [Fits, row_count, htotal, ← show ∀ b, r b =
    (GrayGridComponent.falseRows x b).card from fun _ => rfl, Fin.sum_univ_three]
  constructor
  · rintro (hp | ⟨b, hb, hother⟩)
    · simp [hp]
    · constructor
      · intro c
        by_cases h : c = b
        · simpa [h, hb]
        · simp [hother c h]
      · fin_cases b <;> simp_all
  · rintro ⟨h, htot⟩
    by_cases hall : ∀ b, r b = 1
    · exact Or.inl hall
    · push Not at hall
      obtain ⟨b, hb⟩ := hall
      have hb0 : r b = 0 := by have := h b; omega
      refine Or.inr ⟨b, hb0, fun c hc => ?_⟩
      have h0 := h 0
      have h1 := h 1
      have h2 := h 2
      have htot' : 2 ≤ r 0 + r 1 + r 2 := by
        simpa only [Fin.sum_univ_three] using htot
      clear h htot hb
      fin_cases b
      · change r 0 = 0 at hb0
        fin_cases c
        · exact (hc rfl).elim
        · change r 1 = 1
          omega
        · change r 2 = 1
          omega
      · change r 1 = 0 at hb0
        fin_cases c
        · change r 0 = 1
          omega
        · exact (hc rfl).elim
        · change r 2 = 1
          omega
      · change r 2 = 0 at hb0
        fin_cases c
        · change r 0 = 1
          omega
        · change r 1 = 1
          omega
        · exact (hc rfl).elim

private def vertexOf (s : Finset (Fin 9)) : Vertex := fun i => decide (i ∈ s)

private theorem vertexOf_insert (s : Finset (Fin 9)) (j : Fin 9) (hj : j ∉ s) :
    vertexOf (insert j s) = BalancedCriticalSpectrum.flip (vertexOf s) j := by
  funext i
  by_cases hi : i = j
  · subst i
    simp [vertexOf, BalancedCriticalSpectrum.flip, hj]
  · simp [vertexOf, BalancedCriticalSpectrum.flip, hi]

private theorem affine_of_flip_equivariant (g : Vertex ≃ Vertex) (p : Equiv.Perm (Fin 9))
    (hg : ∀ x j, g (BalancedCriticalSpectrum.flip x j) =
      BalancedCriticalSpectrum.flip (g x) (p j)) :
    ∀ x i, g x (p i) = (x i != g origin (p i)) := by
  have hs : ∀ (s : Finset (Fin 9)) i, g (vertexOf s) (p i) =
      (vertexOf s i != g origin (p i)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro i
      change g origin (p i) = (false != g origin (p i))
      cases g origin (p i) <;> rfl
    | @insert j s hj ih =>
      intro i
      rw [vertexOf_insert s j hj, hg]
      by_cases hi : i = j
      · subst i
        simp [BalancedCriticalSpectrum.flip, ih]
      · have hpi : p i ≠ p j := fun h => hi (p.injective h)
        simp [BalancedCriticalSpectrum.flip, hi, hpi, ih]
  intro x i
  let s := (univ : Finset (Fin 9)).filter (fun j => x j = true)
  have he : vertexOf s = x := by
    funext j
    cases h : x j <;> simp [vertexOf, s, h]
  simpa only [he] using hs s i

/-- Every actual balanced cubic component of order 54 is a Gray placement
with a center and a partition of the nine coordinates into triples. -/
theorem exists_placement_of_balanced_cubic (C : Finset Vertex)
    (hc : C.card = 54)
    (hr : ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3)
    (hb : IsBalanced C) :
    ∃ (block : Fin 9 → Fin 3) (center : Vertex),
      (∀ b, (univ.filter (fun i => block i = b)).card = 3) ∧
      C = placement block center := by
  classical
  obtain ⟨g, p, hg, hC⟩ := CubicFiftyFourReconstruction.gray_reconstruction hr hb hc
  let block := fun i => standardLabels (p.symm i)
  let base := fun i => g origin (p i)
  have he : g = normalize p.symm base := by
    apply Equiv.ext
    intro x
    funext i
    have hx := affine_of_flip_equivariant g p hg x (p.symm i)
    simpa [Q9GrayPlacementNormalForm.normalize, base] using hx
  refine ⟨block, normalize p.symm base allTrue, ?_, ?_⟩
  · intro b
    have eq : (univ.filter (fun i => block i = b)).card =
        (univ.filter (fun i => standardLabels i = b)).card := by
      apply card_bij (fun i _ => p.symm i)
      · intro i hi
        exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩
      · intro a _ b _ h
        exact p.symm.injective h
      · intro i hi
        exact ⟨p i, mem_filter.mpr ⟨mem_univ _, by
          simpa [block] using (mem_filter.mp hi).2⟩, p.symm_apply_apply i⟩
    rw [eq]
    fin_cases b <;> decide +kernel
  · have h := normalize_placement p.symm (Equiv.refl (Fin 3)) standardLabels block
      (fun _ => rfl) base allTrue
    rw [hC, standard_support, he, ← h]
    apply Finset.ext
    intro v
    simp only [Finset.mem_image, Finset.mem_map, Equiv.toEmbedding_apply]

#print axioms exists_placement_of_balanced_cubic

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementReconstruction
