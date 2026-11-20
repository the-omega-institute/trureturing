/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ThreeFlipSpectralLayers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9ThreeFlipSpectralLayers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Signed translation and spectral layers of balanced cubic components in Q9. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeFiftyFourLowerBound
import Mathlib.Combinatorics.SimpleGraph.Bipartite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeFlipSpectralLayers

open scoped Classical BigOperators
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q gamma IsBalanced IsSwitching switchingVector)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeGirth (gamma_anticommute)
open BalancedCubeComponentBoundary (directions regular_directions)
open private flip_injective directions_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open SupportedEigenDimension (supportedEigenSpace mem_supportedEigenSpace_iff)
open private huangMatrix huangMatrix_symmetric cubeParity cubeParity_ne_of_adj from
  D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private switching_sq direction_endpoint_equation from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
open private flip_comm gamma_reverse_three adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private gamma_square from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointEightWord
open private zero_iff_of_reachable from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwoBalancedComponents
open SupportedEigenSaturation (matrix_sq_of_adj)
open private selected_neighbor_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SupportedEigenSaturation
open private matrix_row from
  D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance

/-- The two blocks specify the moving and the fixed coordinates of a three-flip translation. -/
abbrev Coordinates := Fin 3 ⊕ Fin 6 ≃ Fin 9

/-- Combine a moving pattern and a fixed-coordinate vertex in the original coordinate order. -/
def vertex (e : Coordinates) (p : Q 3) (y : Q 6) : Q 9 :=
  fun i => Sum.elim p y (e.symm i)

private def split (e : Coordinates) : Q 9 ≃ Q 3 × Q 6 where
  toFun x := (fun i => x (e (.inl i)), fun j => x (e (.inr j)))
  invFun z := vertex e z.1 z.2
  left_inv x := by
    funext i
    obtain ⟨i, rfl⟩ := e.surjective i
    cases i <;> simp [vertex]
  right_inv z := by
    apply Prod.ext <;> funext i <;> simp [vertex]

@[simp] private theorem vertex_left (e : Coordinates) (p : Q 3) (y : Q 6) (i : Fin 3) :
    vertex e p y (e (.inl i)) = p i := by simp [vertex]

@[simp] private theorem vertex_right (e : Coordinates) (p : Q 3) (y : Q 6) (j : Fin 6) :
    vertex e p y (e (.inr j)) = y j := by simp [vertex]

private theorem vertex_flip_left (e : Coordinates) (p : Q 3) (y : Q 6) (i : Fin 3) :
    vertex e (flip p i) y = flip (vertex e p y) (e (.inl i)) := by
  funext k
  obtain ⟨k, rfl⟩ := e.surjective k
  rcases k with j | j
  · by_cases h : j = i <;> simp [BalancedCriticalSpectrum.flip, h]
  · simp [BalancedCriticalSpectrum.flip]

private theorem vertex_flip_right (e : Coordinates) (p : Q 3) (y : Q 6) (j : Fin 6) :
    vertex e p (flip y j) = flip (vertex e p y) (e (.inr j)) := by
  funext k
  obtain ⟨k, rfl⟩ := e.surjective k
  rcases k with i | i
  · simp [BalancedCriticalSpectrum.flip]
  · by_cases h : i = j <;> simp [BalancedCriticalSpectrum.flip, h]

/-- The antipodal pattern in the three moving coordinates. -/
def antipode (p : Q 3) : Q 3 := fun i => !p i

@[simp] private theorem antipode_antipode (p : Q 3) : antipode (antipode p) = p := by
  funext i
  simp [antipode]

/-- Translate in the three moving coordinates. -/
def translate (e : Coordinates) (x : Q 9) : Q 9 :=
  vertex e (antipode (split e x).1) (split e x).2

@[simp] theorem translate_vertex (e : Coordinates) (p : Q 3) (y : Q 6) :
    translate e (vertex e p y) = vertex e (antipode p) y := by
  simp [translate, show split e (vertex e p y) = (p, y) from (split e).apply_symm_apply (p, y)]

@[simp] theorem translate_involutive (e : Coordinates) (x : Q 9) :
    translate e (translate e x) = x := by
  obtain ⟨⟨p, y⟩, rfl⟩ := (split e).symm.surjective x
  change translate e (translate e (vertex e p y)) = vertex e p y
  simp

private theorem translate_apply (e : Coordinates) (x : Q 9) (i : Fin 9) :
    translate e x i = if (e.symm i).isLeft then !x i else x i := by
  obtain ⟨k, rfl⟩ := e.surjective i
  cases k <;> simp [translate, split, antipode]

/-- Any Boolean mask of weight three specifies a choice of moving and fixed coordinates. -/
theorem exists_coordinates_of_weight_three (v : Q 9)
    (hv : (Finset.univ.filter fun i => v i = true).card = 3) :
    ∃ e : Coordinates, ∀ x : Q 9, translate e x = fun i => x i ^^ v i := by
  let S : Finset (Fin 9) := Finset.univ.filter fun i => v i = true
  have hS : S.card = 3 := hv
  have hT : Fintype.card {i : Fin 9 // i ∉ S} = 6 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe S, hS, Fintype.card_fin]
  let left := (S.equivFinOfCardEq hS).symm
  let right := (Fintype.equivFinOfCardEq hT).symm
  let e : Coordinates :=
    (Equiv.sumCongr left right).trans (Equiv.sumCompl (fun i => i ∈ S))
  refine ⟨e, fun x => funext fun i => ?_⟩
  obtain ⟨j, rfl⟩ := e.surjective i
  rw [translate_apply, Equiv.symm_apply_apply]
  rcases j with a | b
  · have ha : v (e (.inl a)) = true := by
      have h : e (.inl a) ∈ S := (left a).2
      simpa [S] using h
    simp [ha]
  · have hb : v (e (.inr b)) = false := by
      have h : e (.inr b) ∉ S := (right b).2
      cases hv' : v (e (.inr b)) <;> simp_all [S]
    simp [hb]

private theorem translate_flip (e : Coordinates) (x : Q 9) (i : Fin 9) :
    translate e (flip x i) = flip (translate e x) i := by
  funext j
  by_cases hj : j = i
  · subst j
    simp only [translate_apply, BalancedCriticalSpectrum.flip_apply_same]
    cases (e.symm i).isLeft <;> simp
  · simp only [translate_apply, BalancedCriticalSpectrum.flip, Function.update_of_ne hj]

private theorem translate_adj (e : Coordinates) {x y : Q 9} (h : (hypercube 9).Adj x y) :
    (hypercube 9).Adj (translate e x) (translate e y) := by
  obtain ⟨i, rfl⟩ := adjacent_exists_flip h
  rw [translate_flip]
  exact BalancedCriticalSpectrum.flip_adj _ _

private theorem translate_eq_flips (e : Coordinates) (x : Q 9) :
    translate e x = flip (flip (flip x (e (.inl 0))) (e (.inl 1))) (e (.inl 2)) := by
  obtain ⟨⟨p, y⟩, rfl⟩ := (split e).symm.surjective x
  change translate e (vertex e p y) =
    flip (flip (flip (vertex e p y) (e (.inl 0))) (e (.inl 1))) (e (.inl 2))
  rw [translate_vertex, ← vertex_flip_left, ← vertex_flip_left, ← vertex_flip_left]
  congr 1
  funext i
  fin_cases i <;> simp [antipode, BalancedCriticalSpectrum.flip]

private theorem ambient_apply {n : ℕ} (z : Q n → ℝ) (x : Q n) :
    (huangMatrix n).mulVec z x = ∑ i, gamma i z x := by
  simpa only [BalancedCriticalSpectrum.gamma_apply] using matrix_row z x

private abbrev edge (x : Q 9) (i : Fin 9) : ℝ :=
  huangMatrix 9 x (flip x i)

private theorem edge_reverse (x : Q 9) (i : Fin 9) : edge (flip x i) i = edge x i := by
  unfold edge
  rw [BalancedCriticalSpectrum.flip_flip]
  exact huangMatrix_symmetric _ _

private theorem edge_unit (x : Q 9) (i : Fin 9) : edge x i ^ 2 = 1 :=
  matrix_sq_of_adj (BalancedCriticalSpectrum.flip_adj x i)

private theorem exists_translation_sign (e : Coordinates) :
    ∃ theta : Q 9 → ℝ,
      (∀ x, theta (translate e x) * theta x = -1) ∧
      ∀ z : Q 9 → ℝ, (huangMatrix 9).mulVec (fun x => theta (translate e x) * z (translate e x)) =
        fun x => theta (translate e x) * ((huangMatrix 9).mulVec z) (translate e x) := by
  let g : Q 9 ≃ Q 9 := (show Function.Involutive (translate e) from
    translate_involutive e).toPerm (translate e)
  obtain ⟨theta, hunit, hg, hcov⟩ := HuangCubeCovariance.exists_signed_covariance g
    (Equiv.refl (Fin 9)) (translate_flip e)
  have ht (x : Q 9) : theta x ^ 2 = 1 := (sq_eq_one_iff).mpr (hunit x)
  have he (x : Q 9) (i : Fin 9) : edge (translate e x) i =
      theta x * edge x i * theta (flip x i) := by
    have h := hg x i
    change huangMatrix 9 (translate e x) (translate e (flip x i)) = _ at h
    rwa [translate_flip] at h
  refine ⟨theta, ?_, ?_⟩
  · intro x
    let a := e (.inl 0)
    let b := e (.inl 1)
    let c := e (.inl 2)
    have hab : a ≠ b := fun h => (by decide : (0 : Fin 3) ≠ 1)
      (Sum.inl.inj (e.injective h))
    have hac : a ≠ c := fun h => (by decide : (0 : Fin 3) ≠ 2)
      (Sum.inl.inj (e.injective h))
    have hbc : b ≠ c := fun h => (by decide : (1 : Fin 3) ≠ 2)
      (Sum.inl.inj (e.injective h))
    let y := flip x a
    let z := flip y b
    have hx : translate e x = flip z c := translate_eq_flips e x
    have hy : translate e y = flip (flip x c) b := by
      dsimp [y]
      rw [translate_flip, hx]
      dsimp [z, y]
      rw [flip_comm (flip (flip x a) b) c a, flip_comm (flip x a) b a,
        BalancedCriticalSpectrum.flip_flip, flip_comm x b c]
    have hz : translate e z = flip x c := by
      dsimp [z]
      rw [translate_flip, hy, BalancedCriticalSpectrum.flip_flip]
    have hrev := congrFun (gamma_reverse_three hab hac hbc (fun _ => (1 : ℝ))) x
    simp only [BalancedCriticalSpectrum.gamma_apply, Pi.neg_apply, mul_one] at hrev
    change edge x a * (edge y b * edge z c) =
      -(edge x c * (edge (flip x c) b * edge (flip (flip x c) b) a)) at hrev
    have hprod' : edge (translate e x) a * (edge (translate e y) b *
        edge (translate e z) c) =
        -(edge x a * (edge y b * edge z c)) := by
      rw [show translate e x = flip (flip (flip x c) b) a by
        rw [← hy, ← translate_flip, show flip y a = x from
          BalancedCriticalSpectrum.flip_flip x a],
        hy, hz, edge_reverse _ a, edge_reverse _ b, edge_reverse _ c]
      linear_combination hrev
    have htel : edge (translate e x) a * (edge (translate e y) b *
        edge (translate e z) c) =
        (theta x * theta (translate e x)) * (edge x a * (edge y b * edge z c)) := by
      rw [he, he, he, hx]
      change (theta x * edge x a * theta y) *
        ((theta y * edge y b * theta z) * (theta z * edge z c * theta (flip z c))) = _
      calc
        _ = (theta x * theta (flip z c)) *
            (edge x a * (edge y b * edge z c)) * theta y ^ 2 * theta z ^ 2 := by ring
        _ = _ := by rw [ht, ht, mul_one, mul_one]
    have hne (w : Q 9) (i : Fin 9) : edge w i ≠ 0 := by
      intro hc
      have h := edge_unit w i
      simp [hc] at h
    rw [mul_comm (theta (translate e x)) (theta x)]
    apply mul_right_cancel₀ (mul_ne_zero (hne x a) (mul_ne_zero (hne y b) (hne z c)))
    rw [← htel, hprod', neg_one_mul]
  · intro z
    have hsymm (x : Q 9) : g.symm x = translate e x := rfl
    have h := hcov z
    simp only [hsymm] at h
    exact h

/-- A connected nonempty balanced cubic component is moved by any three-flip translation. -/
theorem exists_translate_not_mem (e : Coordinates) (C : Finset (Q 9)) (hC : C.Nonempty)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) : ∃ x ∈ C, translate e x ∉ C := by
  by_contra! hinv
  obtain ⟨a, ha⟩ := hC
  obtain ⟨sigma, hs⟩ := hb
  let z := switchingVector C sigma
  obtain ⟨theta, ht, hcov⟩ := exists_translation_sign e
  let R := fun f : Q 9 → ℝ => fun x => theta (translate e x) * f (translate e x)
  let w := R z
  have hz : z ∈ supportedEigenSpace C := (mem_supportedEigenSpace_iff C z).mpr
    ⟨BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C sigma hr hs,
      fun x hx => by simp [z, switchingVector, hx]⟩
  have hw : w ∈ supportedEigenSpace C := (mem_supportedEigenSpace_iff C w).mpr
    ⟨by
        change (huangMatrix 9).mulVec (fun x => theta (translate e x) * z (translate e x)) = _
        rw [hcov z, hz.1]
        funext x
        change theta (translate e x) * (3 * z (translate e x)) =
          3 * (theta (translate e x) * z (translate e x))
        ring, fun x hx => by
        have hx' : translate e x ∉ C := by
          intro hx'
          exact hx (by simpa using hinv _ hx')
        simp [w, R, hz.2 _ hx']⟩
  have ha' : z a ≠ 0 := by
    have h : z a ^ 2 = 1 := by simpa [z, switchingVector, ha] using switching_sq hs ha
    intro hzero
    simp [hzero] at h
  let c := w a / z a
  let u := w - c • z
  have hu : u ∈ supportedEigenSpace C := (supportedEigenSpace C).sub_mem hw
    ((supportedEigenSpace C).smul_mem c hz)
  have hua : u a = 0 := by
    change w a - w a / z a * z a = 0
    rw [div_mul_cancel₀ _ ha', sub_self]
  have hu0 : u = 0 := by
    funext x
    by_cases hx : x ∈ C
    · exact (zero_iff_of_reachable C u (fun t => (hr.degree_eq t).le) hu.2 hu.1
        (hc.preconnected ⟨a, ha⟩ ⟨x, hx⟩)).mp hua
    · exact hu.2 x hx
  have hratio : w = c • z := sub_eq_zero.mp hu0
  have h : R w a = -z a := by
    simp only [R, w, translate_involutive]
    rw [← mul_assoc, ht, neg_one_mul]
  have hwa : w a = theta (translate e a) * z (translate e a) := rfl
  have hca : w a = c * z a := congrFun hratio a
  have hk : (c ^ 2 + 1) * z a = 0 := by
    have hstep : R w a = c * w a := by
      conv_lhs => rw [hratio]
      change theta (translate e a) * (c * z (translate e a)) = c * w a
      rw [hwa]
      ring
    rw [hstep, hca] at h
    linear_combination h
  exact ha' ((mul_eq_zero.mp hk).resolve_left (by positivity))

/-- In a translation-invariant ambient set, a closed connected balanced cubic component
has no common vertex or edge with its three-flip translate. -/
theorem separated_translate (e : Coordinates) (U C : Finset (Q 9))
    (hU : ∀ x ∈ U, translate e x ∈ U) (hCU : C ⊆ U)
    (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hC : C.Nonempty) (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y) := by
  obtain ⟨a, ha, hta⟩ := exists_translate_not_mem e C hC hc hr hb
  have hdisj (y : (C : Set (Q 9))) : translate e y.1 ∉ C := by
    obtain ⟨walk⟩ := hc.preconnected y ⟨a, ha⟩
    have hwalk {s t : (C : Set (Q 9))}
        (path : ((hypercube 9).induce (C : Set (Q 9))).Walk s t) :
        translate e s.1 ∈ C → translate e t.1 ∈ C := by
      induction path with
      | nil => exact id
      | @cons s b t hsb _ ih =>
        intro hs
        exact ih (hclosed _ hs _ (hU _ (hCU b.2)) (translate_adj e hsb))
    exact fun hy => hta (hwalk walk hy)
  intro x hx y hy
  refine ⟨fun he => hdisj ⟨y, hy⟩ (he ▸ hx), fun ha => ?_⟩
  exact hdisj ⟨y, hy⟩ (hclosed _ hx _ (hU _ (hCU hy)) ha)

#print axioms exists_translate_not_mem
#print axioms separated_translate

/-- The fixed-coordinate vertices occurring at a given moving pattern. -/
def layer (e : Coordinates) (C : Finset (Q 9)) (p : Q 3) : Finset (Q 6) :=
  Finset.univ.filter fun y => vertex e p y ∈ C

/-- The fixed-coordinate fibres meeting the component. -/
def occupied (e : Coordinates) (C : Finset (Q 9)) : Finset (Q 6) :=
  Finset.univ.filter fun y => ∃ p : Q 3, vertex e p y ∈ C

/-- The moving patterns present in a fixed-coordinate fibre. -/
def fibre (e : Coordinates) (C : Finset (Q 9)) (y : Q 6) : Finset (Q 3) :=
  Finset.univ.filter fun p => vertex e p y ∈ C

private def movingDirections (e : Coordinates) (C : Finset (Q 9)) (x : Q 9) :
    Finset (Fin 3) := Finset.univ.filter fun i => flip x (e (.inl i)) ∈ C

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- Evaluate all pairs of the eight moving patterns.
private theorem pattern_cases :
    ∀ p q : Q 3, p = q ∨ (∃ i, q = flip p i) ∨
      p = antipode q ∨ (∃ i, antipode q = flip p i) := by decide

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- Evaluate the local neighbor count at each pattern and edge.
private theorem pattern_edge_degree :
    ∀ p q : Q 3, ∀ i : Fin 3,
      (Finset.univ.filter (fun j => flip q j = p ∨ flip q j = flip p i)).card =
        if q = antipode p ∨ q = antipode (flip p i) then 0 else 1 := by decide

private theorem pair_in_fibre (e : Coordinates) (C : Finset (Q 9))
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y))
    (y : Q 6) {p q : Q 3} (hp : vertex e p y ∈ C) (hq : vertex e q y ∈ C) :
    p = q ∨ ∃ i, q = flip p i := by
  have hs := hsep _ hp _ hq
  rw [translate_vertex] at hs
  rcases pattern_cases p q with h | h | h | ⟨i, hi⟩
  · exact Or.inl h
  · exact Or.inr h
  · exact (hs.1 (congrArg (fun r => vertex e r y) h)).elim
  · exact (hs.2 (by rw [hi, vertex_flip_left]; exact BalancedCriticalSpectrum.flip_adj _ _)).elim

private theorem movingDirections_le_one (e : Coordinates) (C : Finset (Q 9))
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y))
    {x : Q 9} : (movingDirections e C x).card ≤ 1 := by
  obtain ⟨⟨p, y⟩, rfl⟩ := (split e).symm.surjective x
  change (movingDirections e C (vertex e p y)).card ≤ 1
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' : vertex e (flip p i) y ∈ C := by
    simpa [movingDirections, vertex_flip_left] using hi
  have hj' : vertex e (flip p j) y ∈ C := by
    simpa [movingDirections, vertex_flip_left] using hj
  rcases pair_in_fibre e C hsep y hi' hj' with he | ⟨k, hk⟩
  · exact flip_injective p he
  · exfalso
    have hf := cubeParity_ne_of_adj (BalancedCriticalSpectrum.flip_adj p i)
    have hg := cubeParity_ne_of_adj (BalancedCriticalSpectrum.flip_adj p j)
    have hh := cubeParity_ne_of_adj (BalancedCriticalSpectrum.flip_adj (flip p i) k)
    rw [← hk] at hh
    cases h : cubeParity p <;> cases hi : cubeParity (flip p i) <;>
      cases hj : cubeParity (flip p j) <;> simp_all

private theorem movingDirections_card (e : Coordinates) (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y))
    {x : Q 9} (hx : x ∈ C) : (movingDirections e C x).card = 1 := by
  obtain ⟨sigma, hs⟩ := hb
  have hend (i : Fin 3) :
      3 * (BalancedCriticalSpectrum.directionEndpoints C (e (.inl i))).card = C.card := by
    have h := direction_endpoint_equation (d := 3) C sigma hr hs (e (.inl i))
    exact_mod_cast h
  have hsum : (∑ v ∈ C, (movingDirections e C v).card) = C.card := by
    calc
      _ = ∑ i : Fin 3, (BalancedCriticalSpectrum.directionEndpoints C (e (.inl i))).card := by
        simp only [movingDirections, BalancedCriticalSpectrum.directionEndpoints,
          Finset.card_filter]
        rw [Finset.sum_comm]
      _ = _ := by
        have h := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin 3))) rfl
          (fun i _ => hend i)
        rw [← Finset.mul_sum] at h
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
        omega
  have hle (v : Q 9) : (movingDirections e C v).card ≤ 1 :=
    movingDirections_le_one e C hsep
  have hdiff : (∑ v ∈ C, (1 - (movingDirections e C v).card)) = 0 := by
    rw [Finset.sum_tsub_distrib C (fun v _ => hle v), hsum]
    simp
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun v (_ : v ∈ C) =>
    Nat.zero_le (1 - (movingDirections e C v).card))).mp hdiff x hx
  have hlex := hle x
  omega

/-- Every occupied fixed-coordinate fibre is a single edge of the moving cube. -/
theorem fibre_eq_edge (e : Coordinates) (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y))
    (y : Q 6) (hy : y ∈ occupied e C) :
    ∃ p : Q 3, ∃ i : Fin 3, fibre e C y = {p, flip p i} := by
  obtain ⟨p, hp⟩ : ∃ p, vertex e p y ∈ C := by simpa [occupied] using hy
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (movingDirections_card e C hr hb hsep hp)
  refine ⟨p, i, Finset.ext fun q => ?_⟩
  simp only [fibre, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hq
    rcases pair_in_fibre e C hsep y hp hq with h | ⟨j, hj⟩
    · exact Or.inl h.symm
    · right
      have hj' : j ∈ movingDirections e C (vertex e p y) := by
        simpa [movingDirections, ← vertex_flip_left, ← hj] using hq
      have he : j = i := by simpa [hi] using hj'
      simpa [he] using hj
  · rintro (rfl | rfl)
    · exact hp
    · have hi' : i ∈ movingDirections e C (vertex e p y) := by simp [hi]
      simpa [movingDirections, vertex_flip_left] using hi'

private theorem restrictedGamma_squared {n : ℕ} (s : Finset (Fin n)) (z : Q n → ℝ) :
    (∑ i ∈ s, gamma i (∑ j ∈ s, gamma j z)) = (s.card : ℝ) • z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.card_insert_of_notMem ha,
      Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    simp only [map_add, Finset.sum_add_distrib, gamma_square] at *
    rw [ih, map_sum]
    have hanti : (∑ j ∈ s, gamma a (gamma j z)) =
        -(∑ j ∈ s, gamma j (gamma a z)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun j hj =>
        gamma_anticommute (fun h : a = j => ha (by simpa only [h] using hj)) z
    rw [hanti]
    abel

private def fixedOperator (e : Coordinates) (z : Q 9 → ℝ) : Q 9 → ℝ :=
  ∑ j : Fin 6, gamma (e (.inr j)) z

private theorem fixedOperator_square (e : Coordinates) (z : Q 9 → ℝ) :
    fixedOperator e (fixedOperator e z) = (6 : ℝ) • z := by
  let f : Fin 6 → Fin 9 := fun j => e (.inr j)
  have hf : Function.Injective f := fun _ _ h => Sum.inr.inj (e.injective h)
  let s := Finset.univ.image f
  have hcard : s.card = 6 := by simp [s, Finset.card_image_of_injective _ hf]
  have hop (w : Q 9 → ℝ) : fixedOperator e w = ∑ j ∈ s, gamma j w := by
    change fixedOperator e w = ∑ j ∈ Finset.univ.image f, gamma j w
    rw [Finset.sum_image hf.injOn]
    rfl
  rw [hop, hop, restrictedGamma_squared, hcard]
  norm_num

private theorem fixedOperator_apply (e : Coordinates) (z : Q 9 → ℝ) (p : Q 3) (y : Q 6) :
    fixedOperator e z (vertex e p y) =
      ∑ j : Fin 6, edge (vertex e p y) (e (.inr j)) * z (vertex e p (flip y j)) := by
  simp [fixedOperator, Finset.sum_apply, BalancedCriticalSpectrum.gamma_apply, vertex_flip_right]

private theorem fixedOperator_symm (e : Coordinates) (p : Q 3) (z w : Q 9 → ℝ) :
    (∑ y : Q 6, z (vertex e p y) * fixedOperator e w (vertex e p y)) =
      ∑ y : Q 6, fixedOperator e z (vertex e p y) * w (vertex e p y) := by
  simp only [fixedOperator_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := (Finset.univ : Finset (Q 6)))]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  let equiv : Q 6 ≃ Q 6 := (show Function.Involutive (fun y : Q 6 => flip y j) from
    fun y => BalancedCriticalSpectrum.flip_flip y j).toPerm (fun y => flip y j)
  apply Fintype.sum_equiv equiv
  intro y
  change _ = (edge (vertex e p (flip y j)) (e (.inr j)) *
    z (vertex e p (flip (flip y j) j))) * w (vertex e p (flip y j))
  rw [BalancedCriticalSpectrum.flip_flip, vertex_flip_right, edge_reverse]
  ring

private theorem fixedOperator_norm (e : Coordinates) (p : Q 3) (z : Q 9 → ℝ) :
    (∑ y : Q 6, fixedOperator e z (vertex e p y) ^ 2) =
      6 * ∑ y : Q 6, z (vertex e p y) ^ 2 := by
  simp only [pow_two, Finset.mul_sum]
  rw [← fixedOperator_symm e p z (fixedOperator e z), fixedOperator_square]
  apply Finset.sum_congr rfl
  intro y _
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

private theorem moving_sum (e : Coordinates) {C : Finset (Q 9)}
    (sigma : Q 9 → ℝ) (x : Q 9) :
    (∑ i : Fin 3, gamma (e (.inl i)) (switchingVector C sigma) x) =
      ∑ i ∈ movingDirections e C x, edge x (e (.inl i)) * sigma (flip x (e (.inl i))) := by
  simp only [BalancedCriticalSpectrum.gamma_apply, movingDirections, Finset.sum_filter,
    switchingVector, mul_ite, mul_zero]

private theorem fixedOperator_point (e : Coordinates) (C : Finset (Q 9)) (sigma : Q 9 → ℝ)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C sigma)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y))
    (hmoving : ∀ x ∈ C, (movingDirections e C x).card = 1)
    (p : Q 3) (y : Q 6) :
    fixedOperator e (switchingVector C sigma) (vertex e p y) ^ 2 +
      (if y ∈ layer e C p then 1 else 0) + (if y ∈ layer e C (antipode p) then 1 else 0) =
      (if y ∈ layer e C p then 4 else 0) + (if y ∈ occupied e C then 1 else 0) := by
  let x := vertex e p y
  have h := congrFun (BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C sigma hr hs) x
  rw [ambient_apply, ← Equiv.sum_comp e, Fintype.sum_sum_type] at h
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have hsum : (∑ i ∈ movingDirections e C x,
      edge x (e (.inl i)) * sigma (flip x (e (.inl i)))) +
      fixedOperator e (switchingVector C sigma) x = 3 * switchingVector C sigma x := by
    simpa only [fixedOperator, Finset.sum_apply, moving_sum, Nat.cast_ofNat] using h
  have hmem (q : Q 3) : y ∈ layer e C q ↔ vertex e q y ∈ C := by simp [layer]
  by_cases hx : x ∈ C
  · have hy : y ∈ occupied e C := by
      simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨p, hx⟩
    have ha : y ∉ layer e C (antipode p) := by
      intro ha
      exact (hsep _ hx _ ((hmem _).mp ha)).1
        (by simp [x])
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (hmoving _ hx)
    have hi' : flip x (e (.inl i)) ∈ C := by
      have : i ∈ movingDirections e C x := by simp [hi]
      simpa [movingDirections] using this
    rw [hi, Finset.sum_singleton] at hsum
    have hsign : edge x (e (.inl i)) = sigma x * sigma (flip x (e (.inl i))) :=
      hs.2 x hx _ hi' (BalancedCriticalSpectrum.flip_adj _ _)
    rw [hsign, mul_assoc, ← pow_two, switching_sq hs hi', mul_one] at hsum
    have hpoint : fixedOperator e (switchingVector C sigma) x = 2 * sigma x := by
      rw [show switchingVector C sigma x = sigma x by simp [switchingVector, hx]] at hsum
      linarith
    change fixedOperator e (switchingVector C sigma) x ^ 2 + _ + _ = _
    rw [hpoint, mul_pow, switching_sq hs hx]
    have hxp : y ∈ layer e C p := (hmem p).mpr hx
    norm_num [hxp, ha, hy]
  · have hx' : y ∉ layer e C p := fun hp => hx ((hmem _).mp hp)
    rw [show switchingVector C sigma x = 0 by simp [switchingVector, hx], mul_zero] at hsum
    by_cases hy : y ∈ occupied e C
    · obtain ⟨q, i, hf⟩ := fibre_eq_edge e C hr ⟨sigma, hs⟩ hsep y hy
      have hC (r : Q 3) : vertex e r y ∈ C ↔ r = q ∨ r = flip q i := by
        have h : r ∈ fibre e C y ↔ r ∈ ({q, flip q i} : Finset (Q 3)) := by rw [hf]
        simpa [fibre] using h
      have hm : (movingDirections e C x).card =
          if p = antipode q ∨ p = antipode (flip q i) then 0 else 1 := by
        have hq : movingDirections e C x =
            Finset.univ.filter (fun j => flip p j = q ∨ flip p j = flip q i) := by
          ext j
          simp [movingDirections, x, ← vertex_flip_left, hC]
        rw [hq]
        exact pattern_edge_degree q p i
      have hanti : y ∈ layer e C (antipode p) ↔
          p = antipode q ∨ p = antipode (flip q i) := by
        rw [hmem, hC]
        have hh (r : Q 3) : antipode p = r ↔ p = antipode r :=
          ⟨fun h => by rw [← h, antipode_antipode], fun h => by rw [h, antipode_antipode]⟩
        simp only [hh]
      by_cases ha : y ∈ layer e C (antipode p)
      · rw [ite_eq_left (hanti.mp ha)] at hm
        rw [Finset.card_eq_zero.mp hm, Finset.sum_empty, zero_add] at hsum
        change fixedOperator e (switchingVector C sigma) x ^ 2 + _ + _ = _
        norm_num [hsum, hx', hy, ha]
      · rw [ite_eq_right (fun h => ha (hanti.mpr h))] at hm
        obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hm
        have hj' : flip x (e (.inl j)) ∈ C := by
          have : j ∈ movingDirections e C x := by simp [hj]
          simpa [movingDirections] using this
        rw [hj, Finset.sum_singleton] at hsum
        have hsquare : fixedOperator e (switchingVector C sigma) x ^ 2 = 1 := by
          have hpoint : fixedOperator e (switchingVector C sigma) x =
              -(edge x (e (.inl j)) * sigma (flip x (e (.inl j)))) := by linarith
          rw [hpoint, neg_sq, mul_pow, edge_unit, switching_sq hs hj', one_mul]
        change fixedOperator e (switchingVector C sigma) x ^ 2 + _ + _ = _
        simp [hsquare, hx', hy, ha]
    · have hout (q : Q 3) : vertex e q y ∉ C := fun hq =>
        hy (by simpa [occupied] using (show ∃ p, vertex e p y ∈ C from ⟨q, hq⟩))
      have hempty : movingDirections e C x = ∅ := by
        ext i
        simp [movingDirections, x, ← vertex_flip_left, hout]
      rw [hempty, Finset.sum_empty, zero_add] at hsum
      change fixedOperator e (switchingVector C sigma) x ^ 2 + _ + _ = _
      simp [hsum, hy, hmem, hout]

/-- Every moving-pattern layer satisfies the exact signed norm equation. -/
theorem layer_card_equation (e : Coordinates) (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y))
    (p : Q 3) :
    3 * (layer e C p).card + (layer e C (antipode p)).card = (occupied e C).card := by
  obtain ⟨sigma, hs⟩ := hb
  have hmoving (x : Q 9) (hx : x ∈ C) : (movingDirections e C x).card = 1 :=
    movingDirections_card e C hr ⟨sigma, hs⟩ hsep hx
  have hnorm := fixedOperator_norm e p (switchingVector C sigma)
  have hz (y : Q 6) : switchingVector C sigma (vertex e p y) ^ 2 =
      if y ∈ layer e C p then 1 else 0 := by
    by_cases hy : vertex e p y ∈ C
    · simpa [switchingVector, layer, hy] using switching_sq hs hy
    · simp [switchingVector, layer, hy]
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Q 6))) rfl
    (fun y _ => fixedOperator_point e C sigma hr hs hsep hmoving p y)
  simp only [Finset.sum_add_distrib, hnorm, hz] at hsum
  have hi (S : Finset (Q 6)) (a : ℝ) :
      (∑ y : Q 6, if y ∈ S then a else 0) = (S.card : ℝ) * a := by
    rw [← Finset.sum_filter]
    simp
  simp only [hi, mul_one] at hsum
  have he : 3 * ((layer e C p).card : ℝ) + ((layer e C (antipode p)).card : ℝ) =
      ((occupied e C).card : ℝ) := by linarith
  exact_mod_cast he

#print axioms layer_card_equation

private theorem layer_fixed_degree (e : Coordinates) (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y))
    (p : Q 3) (y : (layer e C p : Set (Q 6))) :
    ((hypercube 6).induce (layer e C p : Set (Q 6))).degree y = 2 := by
  let x := vertex e p y.1
  have hx : x ∈ C := by simpa [layer, x] using y.2
  have hsplit : (directions C x).card =
      (movingDirections e C x).card + (directions (layer e C p) y.1).card := by
    simp only [directions, movingDirections, Finset.card_filter]
    rw [← Equiv.sum_comp e, Fintype.sum_sum_type]
    simp [x, ← vertex_flip_right, layer]
  rw [regular_directions C hr hx, movingDirections_card e C hr hb hsep hx,
    directions_card] at hsplit
  have hn : ((layer e C p).filter fun v => (hypercube 6).Adj y.1 v) =
      (hypercube 6).neighborFinset y.1 ∩ layer e C p := by
    ext v
    simp [SimpleGraph.mem_neighborFinset, and_comm]
  rw [hn, selected_neighbor_card y.2] at hsplit
  change (3 : ℕ) = 1 + ((hypercube 6).induce (layer e C p : Set (Q 6))).degree y at hsplit
  omega

/-- Count a layer on a specified parity side of the fixed-coordinate cube. -/
def paritySide (S : Finset (Q 6)) (b : Bool) : Finset (Q 6) :=
  S.filter fun y => cubeParity y = b

private theorem paritySide_add (S : Finset (Q 6)) :
    (paritySide S false).card + (paritySide S true).card = S.card := by
  have hu : paritySide S false ∪ paritySide S true = S := by
    ext y
    cases h : cubeParity y <;> simp [paritySide, h]
  have hd : Disjoint (paritySide S false) (paritySide S true) := by
    apply Finset.disjoint_left.mpr
    intro y hy hz
    have hf := (Finset.mem_filter.mp hy).2
    have ht := (Finset.mem_filter.mp hz).2
    rw [hf] at ht
    contradiction
  rw [← Finset.card_union_of_disjoint hd, hu]

private theorem layer_parity_equal (e : Coordinates) (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y))
    (p : Q 3) :
    (paritySide (layer e C p) false).card = (paritySide (layer e C p) true).card := by
  let L := layer e C p
  let P (b : Bool) : Finset (L : Set (Q 6)) :=
    Finset.univ.filter fun y => cubeParity y.1 = b
  let G := (hypercube 6).induce (L : Set (Q 6))
  have hbip : G.IsBipartiteWith (P false : Set _) (P true : Set _) := by
    constructor
    · apply Set.disjoint_left.mpr
      intro y hy hz
      simp [P] at hy hz
      simp [hy] at hz
    · intro a b hab
      have hne := cubeParity_ne_of_adj (show (hypercube 6).Adj a.1 b.1 from hab)
      cases ha : cubeParity a.1 <;> cases hb : cubeParity b.1 <;> simp_all [P]
  have h := SimpleGraph.isBipartiteWith_sum_degrees_eq hbip
  have hd (y : (L : Set (Q 6))) : G.degree y = 2 := layer_fixed_degree e C hr hb hsep p y
  have hdegrees (b : Bool) : (∑ y ∈ P b, G.degree y) = (P b).card * 2 :=
    Finset.sum_const_nat (fun y _ => hd y)
  rw [hdegrees false, hdegrees true] at h
  have hc (b : Bool) : (P b).card = (paritySide L b).card := by
    apply Finset.card_bij (fun y _ => y.1)
    · intro y hy
      exact Finset.mem_filter.mpr ⟨y.2, by simpa [P] using hy⟩
    · intro a _ b _ h
      exact Subtype.ext h
    · intro y hy
      have hy' := Finset.mem_filter.mp hy
      exact ⟨⟨y, hy'.1⟩, by simpa [P] using hy'.2, rfl⟩
  rw [hc false, hc true] at h
  change (paritySide L false).card = (paritySide L true).card
  omega

/-- The fixed-coordinate cube is bipartite, and each selected layer has equal parts. -/
theorem layer_card_even (e : Coordinates) (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y))
    (p : Q 3) : Even (layer e C p).card := by
  have h := paritySide_add (layer e C p)
  rw [← layer_parity_equal e C hr hb hsep p] at h
  exact ⟨(paritySide (layer e C p) false).card, h.symm⟩

private theorem card_fibre (e : Coordinates) (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y))
    (y : Q 6) :
    (fibre e C y).card = if y ∈ occupied e C then 2 else 0 := by
  by_cases hy : y ∈ occupied e C
  · obtain ⟨p, i, h⟩ := fibre_eq_edge e C hr hb hsep y hy
    have hne : p ≠ flip p i := (hypercube 3).ne_of_adj (BalancedCriticalSpectrum.flip_adj p i)
    simp [h, hne, hy]
  · have hempty : fibre e C y = ∅ := by
      ext p
      have hp : vertex e p y ∉ C := fun hp =>
        hy (by simpa [occupied] using (show ∃ q, vertex e q y ∈ C from ⟨p, hp⟩))
      simp [fibre, hp]
    simp [hempty, hy]

private theorem parity_fibre_sum (e : Coordinates) (C : Finset (Q 9))
    (b : Bool) :
    (∑ p : Q 3, (paritySide (layer e C p) b).card) =
      ∑ y : Q 6, if cubeParity y = b then (fibre e C y).card else 0 := by
  have h (p : Q 3) : paritySide (layer e C p) b =
      Finset.univ.filter (fun y => cubeParity y = b ∧ vertex e p y ∈ C) := by
    ext y
    simp [paritySide, layer, and_comm]
  simp only [h, fibre, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : cubeParity y = b <;> simp [hy]

private theorem card_sum_fibre (e : Coordinates) (C : Finset (Q 9)) :
    C.card = ∑ y : Q 6, (fibre e C y).card := by
  have h : C = Finset.univ.filter (fun x : Q 9 => x ∈ C) := by ext x; simp
  conv_lhs => rw [h]
  simp only [fibre, Finset.card_filter]
  rw [← Equiv.sum_comp (split e).symm, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

/-- The three-flip separation forces component order 96, layer order 12 and exactly
24 occupied fibres on each parity side of the fixed-coordinate cube. -/
theorem component_and_fibre_cards (e : Coordinates) (C : Finset (Q 9)) (hC : C.Nonempty)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    (hsep : ∀ x ∈ C, ∀ y ∈ C, x ≠ translate e y ∧ ¬ (hypercube 9).Adj x (translate e y)) :
    C.card = 96 ∧ (occupied e C).card = 48 ∧
      (∀ p : Q 3, (layer e C p).card = 12) ∧
      ∀ b : Bool, (paritySide (occupied e C) b).card = 24 := by
  have hf := card_fibre e C hr hb hsep
  have hc : C.card = 2 * (occupied e C).card := by
    rw [card_sum_fibre e C, show (∑ y : Q 6, (fibre e C y).card) =
      ∑ y : Q 6, if y ∈ occupied e C then 2 else 0 from Finset.sum_congr rfl (fun y _ => hf y),
      ← Finset.sum_filter]
    simp [Nat.mul_comm]
  have hl (p : Q 3) : 4 * (layer e C p).card = (occupied e C).card := by
    have h₁ := layer_card_equation e C hr hb hsep p
    have h₂ := layer_card_equation e C hr hb hsep (antipode p)
    rw [antipode_antipode] at h₂
    omega
  have hmin : 54 ≤ C.card := by
    by_contra! h
    exact BalancedCubeFiftyFourLowerBound.result ⟨C, hC, hr, hb, h⟩
  have hmax : (occupied e C).card ≤ 64 := by
    simpa [Sensitivity.Q.card] using Finset.card_le_univ (occupied e C)
  have he := BalancedCriticalSpectrum.direction_edge_count (d := 3) C hr hb (e (.inl 0))
  let p₀ : Q 3 := fun _ => false
  obtain ⟨k, hk⟩ := layer_card_even e C hr hb hsep p₀
  have hp₀ := hl p₀
  have hm : (occupied e C).card = 48 := by
    have hwindow : ∀ t : Fin 65, 27 ≤ t.val → t.val % 8 = 0 → t.val % 3 = 0 →
        t.val = 48 := by decide
    have hlo : 27 ≤ (occupied e C).card := by omega
    have h8 : (occupied e C).card % 8 = 0 := by omega
    have h3 : (occupied e C).card % 3 = 0 := by omega
    exact hwindow ⟨(occupied e C).card, Nat.lt_succ_of_le hmax⟩ hlo h8 h3
  have hL (p : Q 3) : (layer e C p).card = 12 := by have := hl p; omega
  refine ⟨by omega, hm, hL, fun b => ?_⟩
  have hp (p : Q 3) : (paritySide (layer e C p) b).card = 6 := by
    have h₁ := paritySide_add (layer e C p)
    have h₂ := layer_parity_equal e C hr hb hsep p
    have h₃ := hL p
    cases b <;> omega
  have hcount := parity_fibre_sum e C b
  simp only [hp, hf, Finset.sum_const, Finset.card_univ, Sensitivity.Q.card, nsmul_eq_mul] at hcount
  have hsum : (∑ y : Q 6, if cubeParity y = b then
      (if y ∈ occupied e C then 2 else 0) else 0) =
        2 * (paritySide (occupied e C) b).card := by
    have h : paritySide (occupied e C) b =
        Finset.univ.filter (fun y => cubeParity y = b ∧ y ∈ occupied e C) := by
      ext y
      simp [paritySide, and_comm]
    rw [h, Finset.card_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    by_cases ha : cubeParity y = b <;> by_cases hb : y ∈ occupied e C <;> simp [ha, hb]
  rw [hsum] at hcount
  norm_num at hcount
  omega

/-- A closed nonempty balanced cubic component rules out an ambient two-flip symmetry. -/
theorem two_flip_not_preserving (U C : Finset (Q 9)) (hCU : C ⊆ U) (hC : C.Nonempty)
    (hclosed : ∀ x ∈ C, ∀ y ∈ U, (hypercube 9).Adj x y → y ∈ C)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C)
    {i j : Fin 9} (hij : i ≠ j) :
    ¬ (∀ x ∈ U, flip (flip x i) j ∈ U) := by
  intro hinv
  have he := BalancedCriticalSpectrum.direction_edge_count (d := 3) C hr hb i
  have hc := Finset.card_pos.mpr hC
  have hpos : 0 < BalancedCriticalSpectrum.directionEdges C i := by omega
  change 0 < (C.filter (fun x => x i = false ∧ flip x i ∈ C)).card at hpos
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
  obtain ⟨hxC, _, hxi⟩ := Finset.mem_filter.mp hx
  have hxjU : flip x j ∈ U := by
    simpa only [BalancedCriticalSpectrum.flip_flip] using hinv (flip x i) (hCU hxi)
  have hxj := hclosed x hxC (flip x j) hxjU (BalancedCriticalSpectrum.flip_adj _ _)
  have hxij := hclosed (flip x i) hxi (flip (flip x i) j) (hinv x (hCU hxC))
    (BalancedCriticalSpectrum.flip_adj _ _)
  exact BalancedCubeGirth.no_selected_square hb hij hxC hxi hxj hxij

#print axioms two_flip_not_preserving
#print axioms exists_coordinates_of_weight_three
#print axioms fibre_eq_edge
#print axioms layer_card_even
#print axioms component_and_fibre_cards

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ThreeFlipSpectralLayers
