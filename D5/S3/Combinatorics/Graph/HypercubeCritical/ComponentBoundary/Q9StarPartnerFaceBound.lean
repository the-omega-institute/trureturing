/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9StarPartnerFaceBound
   generality: I
   mirror-B: none(waiver:standalone-research-source)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Three-face occupancy inequalities for the explicit nine-cube star. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerEdgeBound

/-! The profile weights are from `q9-star-partner-face-hull-certificate.json`.
The translated faces are parametrized by the three base-pair permutations,
the independent diagonal swaps, and the outer coordinate permutations. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerFaceBound

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced direction_edge_count)
open BalancedCubeGirth (no_selected_square)
open Q9StarPartnerBound (Sstar)
open private kind B orbitSize eligible_of_separated partner_subset_B from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerBound
open private Variable Variable.vertex Variable.edge
  Constraint Constraint.degree Constraint.internal Constraint.occupancyCap
  Constraint.source Constraint.target Constraint.overlap Constraint.edgeCap orbitTypes
  Q9StarPartnerEdgeBound.multiplicity occupancy edgeCount value
  orbit selected darts terms rhs evaluate allowedWeight sourceType scaledTerms
  evaluate_by_coefficient coefficient evaluate_combined weighted_sum_le
  objectiveTerms objective_eq from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerEdgeBound
open private flip_comm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private no_selected_reverse_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

local notation "flip" => BalancedCriticalSpectrum.flip

private abbrev Code := Fin 512
private abbrev Corner := Fin 8
private abbrev Axis := Fin 3

private def point (v : Code) : Q 9 := fun i => v.val.testBit i.val

private def encode (v : Q 9) : Code :=
  Fin.ofNat 512 (((List.finRange 9).map fun i => if v i then 2 ^ i.val else 0).sum)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check both inverse identities on the 512 labels.
private theorem point_inverse :
    (∀ v, encode (point v) = v) ∧ (∀ v, point (encode v) = v) := by decide +kernel

private def pointEquiv : Code ≃ Q 9 :=
  ⟨point, encode, point_inverse.1, point_inverse.2⟩

private def toggle {n : Nat} [NeZero n] (v : Fin n) (i : Nat) : Fin n :=
  Fin.ofNat n (v.val ^^^ 2 ^ i)

private theorem point_toggle (v : Code) (i : Fin 9) :
    point (toggle v i.val) = flip (point v) i := by
  funext j
  change ((v.val ^^^ 2 ^ i.val) % 2 ^ 9).testBit j.val =
    Function.update (point v) i (!(point v i)) j
  rw [Nat.testBit_mod_two_pow, Nat.testBit_xor, Nat.testBit_two_pow]
  have hj : j.val < 9 := j.isLt
  by_cases h : j = i
  · subst j
    simp [hj, point]
  · have hv : i.val ≠ j.val := fun e => h (Fin.ext e.symm)
    simp [hj, hv, h, point]

private structure Face where
  origin : Code
  axes : Axis → Fin 9

private def flipCode (v : Code) (i : Fin 9) : Code := toggle v i.val

private theorem flipCode_comm (v : Code) (i j : Fin 9) :
    flipCode (flipCode v i) j = flipCode (flipCode v j) i := by
  apply pointEquiv.injective
  change point (flipCode (flipCode v i) j) = point (flipCode (flipCode v j) i)
  simp only [flipCode, point_toggle, flip_comm]

@[simp] private theorem flipCode_twice (v : Code) (i : Fin 9) :
    flipCode (flipCode v i) i = v := by
  apply pointEquiv.injective
  change point (flipCode (flipCode v i) i) = point v
  simp only [flipCode, point_toggle, BalancedCriticalSpectrum.flip_flip]

private def faceCode (f : Face) (p : Corner) : Code :=
  let a := if p.val.testBit 0 then flipCode f.origin (f.axes 0) else f.origin
  let b := if p.val.testBit 1 then flipCode a (f.axes 1) else a
  if p.val.testBit 2 then flipCode b (f.axes 2) else b

private theorem face_toggle (f : Face) (p : Corner) (i : Axis) :
    faceCode f (toggle p i.val) = flipCode (faceCode f p) (f.axes i) := by
  fin_cases p <;> fin_cases i <;>
    (simp (config := { decide := true }) [faceCode, flipCode_comm] <;>
      rw [flipCode_comm f.origin (f.axes 0) (f.axes 1)])

private def mask (D : Finset (Q 9)) (f : Face) (p : Corner) : Bool :=
  decide (point (faceCode f p) ∈ D)

private def step (p : Corner) (i : Axis) : Corner := toggle p i.val

private def squares : List (Corner × Axis × Axis) :=
  [(0,0,1), (4,0,1), (0,0,2), (2,0,2), (0,1,2), (1,1,2)]

/-- A hexagon is the union of three-step paths whose direction lists are reversed. -/
private def hexagons : List (Corner × Axis × Axis × Axis) :=
  [(1,1,0,2), (0,1,0,2), (0,0,1,2), (0,0,2,1)]

private def squareFree (s : Corner → Bool) : Prop :=
  ∀ t ∈ squares, ¬(s t.1 = true ∧ s (step t.1 t.2.1) = true ∧
    s (step t.1 t.2.2) = true ∧ s (step (step t.1 t.2.1) t.2.2) = true)

private def hexagonFree (s : Corner → Bool) : Prop :=
  ∀ t ∈ hexagons,
    let (p, i, j, k) := t
    ¬(s p = true ∧ s (step p i) = true ∧ s (step (step p i) j) = true ∧
      s (step (step (step p i) j) k) = true ∧
      s (step p k) = true ∧ s (step (step p k) j) = true)

private instance (s : Corner → Bool) : Decidable (squareFree s) := by
  unfold squareFree
  infer_instance

private instance (s : Corner → Bool) : Decidable (hexagonFree s) := by
  unfold hexagonFree
  infer_instance

private def localCard (s : Corner → Bool) : Nat := ((List.finRange 8).filter s).length

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
-- Check all 256 corner patterns against the listed squares and hexagons.
private theorem local_card_bound : ∀ s : Corner → Bool,
    squareFree s → hexagonFree s → localCard s ≤ 5 := by decide +kernel

private theorem translated_face_constraints {D : Finset (Q 9)} (hb : IsBalanced D)
    (f : Face) (hf : Function.Injective f.axes) :
    squareFree (mask D f) ∧ localCard (mask D f) ≤ 5 := by
  have hflip (p : Corner) (i : Axis) :
      point (faceCode f (step p i)) = flip (point (faceCode f p)) (f.axes i) := by
    rw [step, face_toggle, flipCode, point_toggle]
  have hs : squareFree (mask D f) := by
    rintro ⟨p,i,j⟩ ht ⟨hp, hi, hj, hij⟩
    have hne : i ≠ j := by
      have h : ∀ t ∈ squares, t.2.1 ≠ t.2.2 := by decide +kernel
      exact h _ ht
    simp only [mask, decide_eq_true_eq, hflip] at hp hi hj hij
    exact no_selected_square hb (fun e => hne (hf e)) hp hi hj hij
  refine ⟨hs, local_card_bound _ hs ?_⟩
  rintro ⟨p,i,j,k⟩ ht ⟨hp, hi, hij, hijk, hk, hkj⟩
  have h : ∀ t ∈ hexagons,
      let (p,i,j,k) := t
      i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ step (step (step p i) j) k = step (step (step p k) j) i := by
    decide +kernel
  obtain ⟨hnij, hnik, hnjk, hend⟩ := h _ ht
  have he := congrArg (fun u => point (faceCode f u)) hend
  simp only [mask, decide_eq_true_eq, hflip] at hp hi hij hijk hk hkj he
  exact no_selected_reverse_three hb
    (fun e => hnij (hf e)) (fun e => hnik (hf e)) (fun e => hnjk (hf e))
    hp hi hij hijk hk hkj (he ▸ hijk) he

private def axesOf (a b c : Fin 9) : Axis → Fin 9 := ![a, b, c]

/-- A permutation is specified by the destinations of coordinates 0, 1, and 2. -/
private def permutations : List (Axis → Axis) :=
  [![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0]]

private abbrev Symmetry := (Axis → Axis) × Corner × (Axis → Axis)

private def symmetries : List Symmetry :=
  permutations.flatMap fun pairs =>
    (List.finRange 8).flatMap fun swaps =>
      permutations.map fun outer => (pairs, swaps, outer)

private def moveAxis (g : Symmetry) (i : Fin 9) : Fin 9 :=
  if h : i.val < 6 then
    let p : Axis := ⟨i.val / 2, by omega⟩
    let j := i.val % 2
    Fin.ofNat 9 (2 * (g.1 p).val + if g.2.1.val.testBit p.val then 1 - j else j)
  else
    let j : Axis := ⟨i.val - 6, by have := i.isLt; omega⟩
    Fin.ofNat 9 (6 + (g.2.2 j).val)

/-- On a swapped pair, coordinate reversal is followed by complementing both bits. -/
private def movePoint (g : Symmetry) (v : Code) : Code :=
  let base (p : Axis) :=
    let digit := v.val / 4 ^ p.val % 4
    let digit' := if g.2.1.val.testBit p.val && (digit == 0 || digit == 3)
      then 3 - digit else digit
    digit' * 4 ^ (g.1 p).val
  let outer (p : Axis) :=
    if v.val.testBit (6 + p.val) then 2 ^ (6 + (g.2.2 p).val) else 0
  Fin.ofNat 512 (base 0 + base 1 + base 2 + outer 0 + outer 1 + outer 2)

private def translate (f : Face) (g : Symmetry) : Face :=
  ⟨movePoint g f.origin, fun i => moveAxis g (f.axes i)⟩

private def axisDistinct (a : Axis → Fin 9) : Prop :=
  a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ a 1 ≠ a 2

private instance (a : Axis → Fin 9) : Decidable (axisDistinct a) := by
  unfold axisDistinct
  infer_instance

private theorem axes_injective (a : Axis → Fin 9) (h : axisDistinct a) :
    Function.Injective a := by
  intro i j hij
  fin_cases i <;> fin_cases j
  all_goals first | rfl | exact (h.1 hij).elim | exact (h.2.1 hij).elim |
    exact (h.2.2 hij).elim | exact (h.1 hij.symm).elim |
    exact (h.2.1 hij.symm).elim | exact (h.2.2 hij.symm).elim

private theorem moveAxis_injective (g : Symmetry) (hg : g ∈ symmetries) :
    Function.Injective (moveAxis g) := by
  have hperms : ∀ p ∈ permutations, Function.Injective p := by decide +kernel
  have hg' : g.1 ∈ permutations ∧ g.2.2 ∈ permutations := by
    simp only [symmetries, List.mem_flatMap, List.mem_map] at hg
    obtain ⟨p, hp, s, _, o, ho, rfl⟩ := hg
    exact ⟨hp, ho⟩
  have hb (i : Fin 9) (hi : i.val < 6) :
      let j : Axis := ⟨i.val / 2, by omega⟩
      (moveAxis g i).val =
        2 * (g.1 j).val + if g.2.1.val.testBit j.val then 1 - i.val % 2 else i.val % 2 := by
    simp only [moveAxis, dite_eq_left hi, Fin.val_ofNat]
    have ht := (g.1 ⟨i.val / 2, by omega⟩).isLt
    split <;> omega
  have ho (i : Fin 9) (hi : ¬i.val < 6) :
      (moveAxis g i).val = 6 + (g.2.2 ⟨i.val - 6, by have := i.isLt; omega⟩).val := by
    simp only [moveAxis, dite_eq_right hi, Fin.val_ofNat]
    have ht := (g.2.2 ⟨i.val - 6, by have := i.isLt; omega⟩).isLt
    omega
  intro i j he
  have h := congrArg Fin.val he
  have hi9 := i.isLt
  have hj9 := j.isLt
  apply Fin.ext
  by_cases hi : i.val < 6 <;> by_cases hj : j.val < 6
  · rw [hb i hi, hb j hj] at h
    let a : Axis := ⟨i.val / 2, by omega⟩
    let b : Axis := ⟨j.val / 2, by omega⟩
    change 2 * (g.1 a).val + (if g.2.1.val.testBit a.val then 1 - i.val % 2 else i.val % 2) =
      2 * (g.1 b).val + (if g.2.1.val.testBit b.val then 1 - j.val % 2 else j.val % 2) at h
    have hab : a = b := hperms _ hg'.1 <| Fin.ext (by split at h <;> split at h <;> omega)
    have hp : i.val / 2 = j.val / 2 := congrArg Fin.val hab
    rw [hab] at h
    split at h <;> omega
  · rw [hb i hi, ho j hj] at h
    have ht := (g.1 ⟨i.val / 2, by omega⟩).isLt
    split at h <;> omega
  · rw [ho i hi, hb j hj] at h
    have ht := (g.1 ⟨j.val / 2, by omega⟩).isLt
    split at h <;> omega
  · rw [ho i hi, ho j hj] at h
    have ht : (⟨i.val - 6, by omega⟩ : Axis) = ⟨j.val - 6, by omega⟩ :=
      hperms _ hg'.2 (Fin.ext (by omega))
    have hz : i.val - 6 = j.val - 6 := congrArg Fin.val ht
    omega

private theorem translated_axes (f : Face) (hf : Function.Injective f.axes)
    (g : Symmetry) (hg : g ∈ symmetries) : Function.Injective (translate f g).axes :=
  (moveAxis_injective g hg).comp hf

private inductive Slot where
  | v (p : Corner)
  | e (p : Corner) (axis : Axis)

private def slotValue (s : Corner → Bool) : Slot → Int
  | .v p => if s p then 1 else 0
  | .e p i => if s p && s (step p i) then 1 else 0

private structure Profile where
  face : Face
  weights : List (Slot × Int)
  bound : Int

private def score (p : Profile) (s : Corner → Bool) : Int :=
  (p.weights.map fun (t, w) => w * slotValue s t).sum

private abbrev Site := Code × Option (Fin 9)

private def site (f : Face) : Slot → Site
  | .v p => (faceCode f p, none)
  | .e p i => (faceCode f p, some (f.axes i))

private def siteValue (D : Finset (Q 9)) (s : Site) : Int :=
  if point s.1 ∈ D then
    match s.2 with
    | none => 1
    | some i => if flip (point s.1) i ∈ D then 1 else 0
  else 0

private theorem siteValue_eq (D : Finset (Q 9)) (f : Face) (t : Slot) :
    siteValue D (site f t) = slotValue (mask D f) t := by
  cases t with
  | v p =>
    by_cases h : point (faceCode f p) ∈ D <;> simp [siteValue, site, slotValue, mask, h]
  | e p i =>
    simp only [siteValue, site, slotValue, Bool.and_eq_true, mask, decide_eq_true_eq,
      step, face_toggle, flipCode, point_toggle]
    by_cases h : point (faceCode f p) ∈ D <;>
      by_cases h' : flip (point (faceCode f p)) (f.axes i) ∈ D <;> simp [h, h']

private def slotVariable (f : Face) : Slot → Variable
  | .v p => Variable.vertex (kind (point (faceCode f p)))
  | .e p i => Variable.edge (kind (point (faceCode f p))) (kind (point (faceCode f (step p i))))

private def capacity : Variable → Nat
  | Variable.vertex q => orbitSize q
  | Variable.edge q r => Q9StarPartnerEdgeBound.multiplicity q r * orbitSize q

private def codesOf (q : Nat × Nat × Nat) : List Code :=
  (List.finRange 512).filter fun v => kind (point v) == q

private def sites : Variable → List Site
  | Variable.vertex q => (codesOf q).map fun v => (v, none)
  | Variable.edge q r => (codesOf q).flatMap fun v =>
      ((List.finRange 9).filter fun i => kind (point (toggle v i.val)) == r).map
        fun i => (v, some i)

private def orbitRepetitions (v : Variable) : Nat := 288 / capacity v

private def siteKey (s : Site) : Nat := 16 * s.1.val + (s.2.map Fin.val).getD 9

/-- Radix partitioning uses structural recursion, so the kernel can evaluate the lists. -/
private def arrange : Nat → List Site → List Site
  | 0, ss => ss
  | _ + 1, [] => []
  | n + 1, s :: ss =>
    (arrange n ((s :: ss).filter fun t => (siteKey t).testBit n)) ++
      arrange n ((s :: ss).filter fun t => !(siteKey t).testBit n)

private theorem split_perm (p : Site → Bool) (ss : List Site) :
    (ss.filter p ++ ss.filter (fun s => !p s)).Perm ss := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    cases hs : p s with
    | false =>
      simp only [List.filter_cons, hs, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      exact List.perm_middle.trans (ih.cons s)
    | true =>
      simp only [List.filter_cons, hs, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
        List.cons_append]
      exact ih.cons s

private theorem arrange_perm (n : Nat) (ss : List Site) : (arrange n ss).Perm ss := by
  induction n generalizing ss with
  | zero => rfl
  | succ n ih =>
    cases ss with
    | nil => rfl
    | cons s ss => exact ((ih _).append (ih _)).trans (split_perm _ (s :: ss))

-- Each row stores the orientation of its actual cube edges and the integer local weights.
private def profiles : List Profile := [
  ⟨⟨200, axesOf 0 1 2⟩,
    [(.v 0, 5015), (.v 2, 15045), (.v 3, 5015), (.v 6, 5015), (.e 0 1, -5015), (.e 3 0, -5015),
     (.e 6 2, -5015)], 15045⟩,
  ⟨⟨224, axesOf 0 1 2⟩,
    [(.v 0, -8424), (.v 1, -6301), (.v 2, -516), (.v 3, -8424), (.v 4, -6301), (.v 5, -2124), (.v
     6, -1543), (.v 7, -6301), (.e 0 0, 9451), (.e 0 1, 3666), (.e 0 2, 9451), (.e 1 2, 6301), (.e
     2 2, 1543), (.e 3 0, 3666), (.e 3 1, 9451), (.e 3 2, 9451), (.e 4 0, 6301), (.e 4 1, 4693),
     (.e 7 0, 4693), (.e 7 1, 6301)], 2053⟩,
  ⟨⟨448, axesOf 0 1 2⟩,
    [(.v 0, -573), (.v 2, 1145), (.v 3, -573), (.v 5, 2290), (.v 6, 1145), (.e 0 0, 1145), (.e 0
     1, 573), (.e 0 2, 1145), (.e 1 2, -1145), (.e 2 2, -1145), (.e 3 0, 573), (.e 3 1, 1145), (.e
     3 2, 1145), (.e 4 0, -1145), (.e 7 1, -1145)], 3435⟩,
  ⟨⟨464, axesOf 0 1 2⟩,
    [(.v 0, 1543), (.v 2, 3085), (.v 3, 1543), (.v 5, -376), (.e 0 1, -1543), (.e 1 2, 125), (.e 3
     0, -1543), (.e 4 0, 125), (.e 7 1, 125)], 3086⟩,
  ⟨⟨40, axesOf 0 1 6⟩,
    [(.v 0, -11089), (.v 3, -11089), (.v 4, -11089), (.v 5, -11089), (.v 7, -11089), (.e 0 1,
     11089), (.e 0 2, 11089), (.e 3 0, 11089), (.e 3 2, 11089), (.e 4 0, 11089), (.e 4 1, 11089),
     (.e 7 0, 11089), (.e 7 1, 11089)], 0⟩,
  ⟨⟨168, axesOf 0 1 6⟩,
    [(.v 0, -3134), (.v 1, -6268), (.v 2, 471), (.v 3, -3134), (.v 6, 471), (.e 0 0, 6268), (.e 0
     1, 3134), (.e 2 2, -471), (.e 3 0, 3134), (.e 3 1, 6268)], 471⟩,
  ⟨⟨404, axesOf 0 1 6⟩,
    [(.v 0, -4749), (.v 2, -3166), (.v 3, -4749), (.e 0 0, 1583), (.e 0 1, 3166), (.e 0 2, 3166),
     (.e 2 2, 3166), (.e 3 0, 3166), (.e 3 1, 1583), (.e 3 2, 3166)], 0⟩,
  ⟨⟨408, axesOf 0 1 6⟩,
    [(.v 5, -16), (.e 4 0, 8), (.e 7 1, 8)], 0⟩,
  ⟨⟨450, axesOf 0 2 4⟩,
    [(.v 0, 801), (.v 2, 401), (.v 3, -200), (.v 4, 401), (.v 5, -200), (.e 0 1, -401), (.e 0 2,
     -401), (.e 1 0, -401), (.e 1 1, 401), (.e 1 2, 401), (.e 3 0, -401), (.e 3 2, 200), (.e 5 0,
     -401), (.e 5 1, 200)], 802⟩,
  ⟨⟨458, axesOf 0 2 4⟩,
    [(.v 1, 1843), (.v 2, 1843), (.v 5, 2765), (.v 6, 2765), (.e 0 2, 1843), (.e 1 2, -1843), (.e
     2 2, -1843), (.e 3 2, 1843), (.e 5 0, -922), (.e 6 1, -922), (.e 7 0, -922), (.e 7 1, -922)],
     5530⟩,
  ⟨⟨144, axesOf 0 2 6⟩,
    [(.v 5, -309), (.v 6, -309), (.e 5 1, 309), (.e 6 0, 309)], 0⟩,
  ⟨⟨386, axesOf 0 2 6⟩,
    [(.v 7, -391), (.e 5 1, 391)], 0⟩,
  ⟨⟨400, axesOf 0 2 6⟩,
    [(.e 3 2, -237)], 0⟩,
  ⟨⟨418, axesOf 0 2 6⟩,
    [(.v 6, -386), (.e 2 2, 386)], 0⟩,
  ⟨⟨10, axesOf 0 6 7⟩,
    [(.v 0, -16586), (.v 2, -8293), (.v 4, -8293), (.e 0 1, 16586), (.e 0 2, 16586), (.e 2 2,
     8293), (.e 4 1, 8293)], 0⟩,
  ⟨⟨40, axesOf 0 6 7⟩,
    [(.v 0, -19671), (.v 2, -19671), (.v 3, -19671), (.v 4, -19671), (.v 5, -19671), (.e 0 1,
     19671), (.e 0 2, 19671), (.e 2 0, 19671), (.e 2 2, 19671), (.e 3 2, 19671), (.e 4 0, 19671),
     (.e 4 1, 19671), (.e 5 1, 19671)], 0⟩,
  ⟨⟨280, axesOf 0 6 7⟩,
    [(.e 6 0, -2095)], 0⟩,
  ⟨⟨282, axesOf 0 6 7⟩,
    [(.v 6, 771), (.v 7, 771), (.e 7 0, -771)], 771⟩,
  ⟨⟨298, axesOf 0 6 7⟩,
    [(.v 0, 129), (.v 2, 129), (.v 3, 129), (.v 4, 129), (.v 5, 129), (.e 1 0, -129), (.e 1 1,
     64), (.e 1 2, 64), (.e 3 0, -129), (.e 3 2, -129), (.e 5 0, -129), (.e 5 1, -129), (.e 7 0,
     129)], 387⟩,
  ⟨⟨10, axesOf 6 7 8⟩,
    [(.v 3, 557), (.v 5, 557), (.v 6, 557), (.v 7, 1671), (.e 3 2, -557), (.e 5 1, -557), (.e 6 0,
     -557)], 1671⟩,
  ⟨⟨42, axesOf 6 7 8⟩,
    [(.v 0, -371), (.v 3, -371), (.v 5, -371), (.v 6, -371), (.e 0 0, 371), (.e 0 1, 371), (.e 0
     2, 371), (.e 1 1, 371), (.e 1 2, 371), (.e 2 0, 371), (.e 2 2, 371), (.e 3 2, 371), (.e 4 0,
     371), (.e 4 1, 371), (.e 5 1, 371), (.e 6 0, 371)], 742⟩
]

-- The ordinary certificate rows are multiplied by 288 to clear the face-averaging
-- denominator. Cap corrections already include this scaling.
private def otherRows : List (Int × Constraint) := [
  (77472, Constraint.degree (0,2,2)),
  (1017216, Constraint.degree (1,1,0)),
  (2016, Constraint.degree (3,0,1)),
  (118944, Constraint.source (0,2,2) (1,2,2)),
  (83520, Constraint.overlap (1,0,3) (1,1,3)),
  (982944, Constraint.target (2,0,0) (2,1,0)),
  (104544, Constraint.source (2,0,1) (3,0,1)),
  (131616, Constraint.overlap (2,0,2) (2,1,2)),
  (94752, Constraint.source (2,0,3) (3,0,3)),
  (652896, Constraint.source (2,1,0) (2,1,1)),
  (-61632, Constraint.internal (0,0,3)),
  (-29664, Constraint.internal (0,1,3)),
  (-167328, Constraint.internal (0,2,2)),
  (65952, Constraint.internal (0,2,3)),
  (106848, Constraint.internal (0,3,2)),
  (-84096, Constraint.internal (0,3,3)),
  (-52704, Constraint.internal (1,0,2)),
  (52704, Constraint.internal (1,0,3)),
  (-98496, Constraint.internal (1,1,2)),
  (98496, Constraint.internal (1,1,3)),
  (-52704, Constraint.internal (1,2,2)),
  (-48384, Constraint.internal (1,2,3)),
  (-982944, Constraint.internal (2,0,0)),
  (-532224, Constraint.internal (2,0,1)),
  (83520, Constraint.internal (2,0,2)),
  (-52704, Constraint.internal (2,0,3)),
  (-652896, Constraint.internal (2,1,1)),
  (23328, Constraint.internal (2,1,2)),
  (-35712, Constraint.internal (2,1,3)),
  (-81504, Constraint.internal (3,0,0)),
  (-25344, Constraint.internal (3,0,1)),
  (-59040, Constraint.internal (3,0,2)),
  (-48096, Constraint.internal (3,0,3)),
  (360, Constraint.occupancyCap (0,0,3)),
  (288, Constraint.occupancyCap (0,2,2)),
  (312, Constraint.occupancyCap (1,0,2)),
  (456, Constraint.occupancyCap (1,1,3)),
  (224, Constraint.occupancyCap (1,2,2)),
  (384, Constraint.occupancyCap (1,2,3)),
  (48, Constraint.occupancyCap (2,0,0)),
  (432, Constraint.occupancyCap (2,0,3)),
  (128, Constraint.occupancyCap (2,1,2)),
  (288, Constraint.occupancyCap (3,0,0)),
  (288, Constraint.occupancyCap (3,0,1)),
  (132, Constraint.edgeCap (0,1,3) (0,2,3)),
  (64, Constraint.edgeCap (0,2,2) (0,2,3)),
  (144, Constraint.edgeCap (0,2,3) (0,3,3)),
  (36, Constraint.edgeCap (1,0,2) (2,0,2)),
  (80, Constraint.edgeCap (1,1,2) (2,1,2)),
  (96, Constraint.edgeCap (2,0,0) (2,0,1)),
  (256, Constraint.edgeCap (2,0,1) (2,0,2)),
  (224, Constraint.edgeCap (2,0,1) (2,1,1)),
  (48, Constraint.edgeCap (2,0,2) (2,0,3)),
  (80, Constraint.edgeCap (2,0,2) (2,1,2)),
  (96, Constraint.edgeCap (2,1,1) (2,1,2)),
  (32, Constraint.edgeCap (2,1,2) (2,1,3)),
  (144, Constraint.edgeCap (3,0,1) (3,0,2)),
  (288, Constraint.edgeCap (3,0,2) (3,0,3))
]


private def uniform (gs : List Symmetry) (f : Face) (t : Slot) : Prop :=
  let v := slotVariable f t
  arrange 13 (gs.map fun g => site (translate f g) t) =
    arrange 13 (List.replicate (orbitRepetitions v) (sites v)).flatten

private instance (gs : List Symmetry) (f : Face) (t : Slot) : Decidable (uniform gs f t) := by
  unfold uniform
  infer_instance

private def localMaximum (p : Profile) : Prop :=
  (∀ s : Corner → Bool, localCard s ≤ 5 → squareFree s → score p s ≤ p.bound) ∧
  (∃ s : Corner → Bool, localCard s ≤ 5 ∧ squareFree s ∧ score p s = p.bound)

private instance (p : Profile) : Decidable (localMaximum p) := by
  unfold localMaximum
  infer_instance

private def validProfile (p : Profile) : Prop :=
  axisDistinct p.face.axes ∧ localMaximum p ∧ ∀ wt ∈ p.weights, uniform symmetries p.face wt.1

private instance (p : Profile) : Decidable (validProfile p) := by
  unfold validProfile
  infer_instance

set_option maxRecDepth 8192 in
set_option maxHeartbeats 12000000 in
-- Check each local maximum and each translated incidence multiset in the kernel.
private theorem profiles_checked (i : Fin profiles.length) :
    validProfile profiles[i.val] := by
  fin_cases i <;> decide +kernel

private theorem codes_sum (q : Nat × Nat × Nat) (f : Q 9 → Int) :
    ((codesOf q).map fun v => f (point v)).sum = ∑ x ∈ orbit q, f x := by
  classical
  have hn : (codesOf q).Nodup := (List.nodup_finRange 512).filter _
  rw [← List.sum_toFinset _ hn]
  apply Finset.sum_bij (fun v _ => point v)
  · intro v hv
    simpa [codesOf, orbit] using hv
  · intro v _ w _ h
    exact pointEquiv.injective h
  · intro x hx
    refine ⟨encode x, ?_, point_inverse.2 x⟩
    simpa [codesOf, orbit, point_inverse.2] using hx
  · intros
    rfl

set_option maxRecDepth 4096 in
private theorem site_sum (D : Finset (Q 9)) (v : Variable) :
    ((sites v).map (siteValue D)).sum = value D v := by
  classical
  cases v with
  | vertex q =>
    have h : (orbit q).filter (· ∈ D) = selected D q := by
      ext x
      simp [orbit, selected, and_comm]
    simp only [sites, List.map_map, Function.comp_def, siteValue, value, occupancy]
    rw [codes_sum q (fun x => if x ∈ D then 1 else 0), ← Finset.sum_filter, h]
    simp
  | edge q r =>
    have hd : darts (selected D q) (selected D r) =
        (orbit q ×ˢ (Finset.univ : Finset (Fin 9))).filter
          (fun p => p.1 ∈ D ∧ kind (flip p.1 p.2) = r ∧ flip p.1 p.2 ∈ D) := by
      apply Finset.ext
      intro p
      simp only [darts, selected, orbit, Finset.mem_filter, Finset.mem_univ,
        Finset.mem_product, true_and, and_true]
      constructor
      · rintro ⟨⟨hx,hq⟩,hy,hr⟩
        exact ⟨hq,hx,hr,hy⟩
      · rintro ⟨hq,hx,hr,hy⟩
        exact ⟨⟨hx,hq⟩,hy,hr⟩
    simp only [value, edgeCount, hd, Finset.card_eq_sum_ones, Nat.cast_sum,
      Finset.sum_filter, Finset.sum_product]
    unfold sites
    rw [List.map_flatMap, List.flatMap_def, List.sum_flatten, List.map_map]
    rw [← codes_sum q (fun x => ∑ i : Fin 9,
      ((if x ∈ D ∧ kind (flip x i) = r ∧ flip x i ∈ D then 1 else 0 : Nat) : Int))]
    apply congrArg List.sum
    apply List.map_congr_left
    intro u _
    simp only [List.map_map, Function.comp_def, siteValue, point_toggle]
    rw [← List.sum_toFinset _ ((List.nodup_finRange 9).filter _)]
    have hf : ((List.finRange 9).filter
        (fun i => kind (flip (point u) i) == r)).toFinset =
        Finset.univ.filter (fun i => kind (flip (point u) i) = r) := by
      ext i
      simp
    rw [hf, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hu : point u ∈ D <;> by_cases hi : flip (point u) i ∈ D <;>
      by_cases ht : kind (flip (point u) i) = r <;> simp [hu, hi, ht]

private theorem replicated_sum (D : Finset (Q 9)) (ss : List Site) (n : Nat) :
    (((List.replicate n ss).flatten).map (siteValue D)).sum =
      (n : Int) * (ss.map (siteValue D)).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons, List.map_append, List.sum_append,
      ih, Nat.cast_succ]
    ring

private theorem slot_sum (D : Finset (Q 9)) (gs : List Symmetry) (f : Face) (t : Slot)
    (h : uniform gs f t) :
    (gs.map fun g => slotValue (mask D (translate f g)) t).sum =
      (orbitRepetitions (slotVariable f t) : Int) * value D (slotVariable f t) := by
  let a := gs.map fun g => site (translate f g) t
  let b := (List.replicate (orbitRepetitions (slotVariable f t))
    (sites (slotVariable f t))).flatten
  have hc : arrange 13 a = arrange 13 b := h
  have hd : (arrange 13 a).Perm b :=
    Eq.mp (congrArg (fun l => l.Perm b) hc.symm) (arrange_perm 13 b)
  have hp : a.Perm b := (arrange_perm 13 a).symm.trans hd
  have he := (hp.map (siteValue D)).sum_eq
  simpa only [a, b, List.map_map, Function.comp_def, siteValue_eq, replicated_sum, site_sum]
    using he

private theorem list_sum_le {α : Type} (l : List α) (f g : α → Int)
    (h : ∀ a ∈ l, f a ≤ g a) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self)
      (ih fun b hb => h b (List.mem_cons_of_mem _ hb))

private theorem list_sum_swap {α β : Type} (as : List α) (bs : List β) (f : α → β → Int) :
    (as.map fun a => (bs.map (f a)).sum).sum =
      (bs.map fun b => (as.map fun a => f a b).sum).sum := by
  have hadd (l : List β) (p q : β → Int) :
      (l.map fun b => p b + q b).sum = (l.map p).sum + (l.map q).sum := by
    induction l with
    | nil => simp
    | cons b cs ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  induction as with
  | nil => simp
  | cons a cs ih => simp only [List.map_cons, List.sum_cons, hadd, ih]

private def faceTerms (p : Profile) : List (Variable × Int) :=
  p.weights.map fun (s, w) =>
    let v := slotVariable p.face s
    (v, w * (orbitRepetitions v : Int))

private def faceRhs (p : Profile) : Int := 288 * p.bound

/-- Sum the local bound on a list of actual cube faces with prescribed incidence counts. -/
private theorem profile_inequality_on (D : Finset (Q 9)) (hb : IsBalanced D)
    (p : Profile) (gs : List Symmetry) (hsize : gs.length = 288)
    (haxes : ∀ g ∈ gs, Function.Injective (translate p.face g).axes)
    (hmax : localMaximum p) (hcounts : ∀ wt ∈ p.weights, uniform gs p.face wt.1) :
    evaluate (value D) (faceTerms p) ≤ faceRhs p := by
  have hsum : (gs.map fun g => score p (mask D (translate p.face g))).sum ≤
      (gs.map fun _ => p.bound).sum := by
    apply list_sum_le
    intro g hg
    obtain ⟨hs, hc⟩ := translated_face_constraints hb _ (haxes g hg)
    exact hmax.1 _ hc hs
  calc
    _ = (gs.map fun g => score p (mask D (translate p.face g))).sum := by
      unfold score
      rw [list_sum_swap]
      simp only [evaluate, faceTerms, List.map_map, Function.comp_def]
      apply congrArg List.sum
      apply List.map_congr_left
      rintro ⟨t, w⟩ ht
      simp only [List.sum_map_mul_left, slot_sum D gs p.face t (hcounts _ ht), mul_assoc]
    _ ≤ _ := hsum
    _ = faceRhs p := by
      simp only [List.map_const', List.sum_replicate, hsize, nsmul_eq_mul, faceRhs]
      rfl

private theorem symmetry_count : symmetries.length = 288 := by decide +kernel

private theorem profile_inequality (D : Finset (Q 9)) (hb : IsBalanced D)
    (p : Profile) (hp : validProfile p) :
    evaluate (value D) (faceTerms p) ≤ faceRhs p :=
  profile_inequality_on D hb p symmetries symmetry_count
    (translated_axes p.face (axes_injective _ hp.1)) hp.2.1 hp.2.2

private def allTerms : List (Variable × Int) :=
  otherRows.flatMap scaledTerms ++ profiles.flatMap faceTerms

private def objective : List (Variable × Int) :=
  objectiveTerms.map fun (v, c) => (v, 1440 * c)

private def allVariables : List Variable := ((objective ++ allTerms).map Prod.fst).dedup

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
-- Compare the integer coefficients after clearing the face-averaging denominator.
private theorem aggregate_checked :
    (∀ wc ∈ otherRows, sourceType wc.2 ∈ orbitTypes ∧ allowedWeight wc.1 wc.2) ∧
    (∀ v ∈ allVariables, coefficient objective v ≤ coefficient allTerms v) ∧
    (otherRows.map fun wc => wc.1 * rhs wc.2).sum + (profiles.map faceRhs).sum = 17065728 := by
  decide +kernel

open Classical in
private theorem bound_by_rows (D : Finset (Q 9))
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D) (hD : ∀ x ∈ D, B x = true) :
    evaluate (value D) allTerms ≤ 17065728 := by
  have hface (p : Profile) (h : p ∈ profiles) :
      evaluate (value D) (faceTerms p) ≤ faceRhs p := by
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp h
    exact profile_inequality D hb p (hi ▸ profiles_checked i)
  have hs (ps : List Profile) :
      evaluate (value D) (ps.flatMap faceTerms) =
        (ps.map fun p => evaluate (value D) (faceTerms p)).sum := by
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.flatMap_cons, evaluate, List.map_append, List.sum_append,
        List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
  calc
    _ = (otherRows.map fun wc => wc.1 * evaluate (value D) (terms wc.2)).sum +
        (profiles.map fun p => evaluate (value D) (faceTerms p)).sum := by
      unfold allTerms
      rw [show evaluate (value D) (otherRows.flatMap scaledTerms ++ profiles.flatMap faceTerms) =
          evaluate (value D) (otherRows.flatMap scaledTerms) +
            evaluate (value D) (profiles.flatMap faceTerms) by
        simp only [evaluate, List.map_append, List.sum_append]]
      rw [evaluate_combined, hs]
    _ ≤ _ := add_le_add (weighted_sum_le D hr hb hD otherRows aggregate_checked.1)
      (list_sum_le _ _ _ hface)
    _ = 17065728 := aggregate_checked.2.2

private theorem scaled_objective (D : Finset (Q 9)) (hD : ∀ x ∈ D, B x = true) :
    evaluate (value D) objective = 144000 * (D.card : Int) := by
  calc
    _ = 1440 * evaluate (value D) objectiveTerms := by
      simp only [evaluate, objective, List.map_map, Function.comp_def, mul_assoc,
        List.sum_map_mul_left]
    _ = _ := by rw [objective_eq D hD]; ring

private theorem objective_le (D : Finset (Q 9)) :
    evaluate (value D) objective ≤ evaluate (value D) allTerms := by
  rw [evaluate_by_coefficient _ objective allVariables.toFinset,
    evaluate_by_coefficient _ allTerms allVariables.toFinset]
  · apply Finset.sum_le_sum
    intro v hv
    apply mul_le_mul_of_nonneg_right (aggregate_checked.2.1 v (List.mem_toFinset.mp hv))
    cases v <;> exact Int.natCast_nonneg _
  · intro t ht
    exact List.mem_toFinset.mpr <| List.mem_dedup.mpr <|
      List.mem_map_of_mem (List.mem_append_right _ ht)
  · intro t ht
    exact List.mem_toFinset.mpr <| List.mem_dedup.mpr <|
      List.mem_map_of_mem (List.mem_append_left _ ht)

open Classical in
/-- Three-face occupancy bounds any disjoint, nonadjacent induced cubic Huang-balanced
partner of the explicit 72-point star by 114 vertices. -/
theorem partner_card_le_114 (D : Finset (Q 9))
    (hdisj : Disjoint Sstar D)
    (hcross : ∀ s ∈ Sstar, ∀ d ∈ D, ¬ (hypercube 9).Adj s d)
    (hr : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced D) : D.card ≤ 114 := by
  have hD := partner_subset_B hr hb (fun _ => eligible_of_separated hdisj hcross)
  have h := (objective_le D).trans (bound_by_rows D hr hb hD)
  rw [scaled_objective D hD] at h
  have hdiv := direction_edge_count (d := 3) D hr hb (0 : Fin 9)
  omega

#print axioms local_card_bound
#print axioms translated_face_constraints
#print axioms profiles_checked
#print axioms profile_inequality
#print axioms aggregate_checked
#print axioms partner_card_le_114

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9StarPartnerFaceBound
