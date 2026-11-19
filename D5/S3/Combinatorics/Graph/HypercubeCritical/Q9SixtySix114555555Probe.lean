import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixAgreementCapacityProbe

/-! Orbit certificates for normalized Q9 deficit profiles. -/

set_option autoImplicit false

open scoped BigOperators
open Finset SimpleGraph
open D5.S3.Combinatorics.Graph.Hypercube
open D5.S3.Combinatorics.Graph.HypercubeCritical
open BalancedCriticalSpectrum (Q IsBalanced direction_edge_count directionEdges)
local notation "flip" => BalancedCriticalSpectrum.flip

open private cubeParity from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private cubic_parity_half_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixSignedModelProbe
open private shell from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtyShellCompositionProbe
open private sixty_six_distance_seven_le_eight from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixShellProbe
open private coordinate_profile_weight_bound from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixDistanceSumProbe
open private distance_seven_agreement_excludes_minority from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixPartnerWeightsProbe
open private orbit_sum_invariant from
  D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe

namespace D5.S3.Combinatorics.Graph.HypercubeCritical

section

variable (deficit : Fin 9 → ℤ)

private abbrev Bits := BitVec 9
private abbrev Vertex := Q 9
private abbrev Variable := Bits ⊕ (Bits × Bits)
private abbrev Term := Variable × ℤ

private abbrev cube := cubeBitVec 9
private def bitFlip (x : Bits) (i : Fin 9) : Bits := x ^^^ BitVec.ofNat 9 (2 ^ i.val)
private def weight (x : Bits) : ℤ := ∑ i, if cube x i then deficit i else 0
private def allowed (x : Bits) : Bool := decide (2 * weight deficit x + 12 ≤ (∑ i, deficit i) + 8)
private def farAgreement (x y : Bits) (i : Fin 9) : Bool :=
  decide (hammingDist (cube x) (cube y) = 7 ∧ cube x i = cube y i)
private def allowedFar (x y : Bits) : Bool :=
  (allowed deficit) y && (List.finRange 9).all fun i =>
    !(cube x i && (cube y i == cube x i) && decide (1 < deficit i))

private def single (x : Bits) (a : ℤ) : Term := (.inl x, a)
private def pair (x y : Bits) (a : ℤ) : Term := (.inr (x, y), a)

private def termsOf {n : ℕ} (p : Fin n → Bool) (t : Fin n → Term) : List Term :=
  ((List.finRange n).filter p).map t

private def cubeTerms (p : Bits → Bool) (t : Bits → Term) : List Term :=
  termsOf (p ∘ BitVec.ofFin) (t ∘ BitVec.ofFin)

private inductive Row where
  | size | parity
  | half (i : Fin 9)
  | direction (i : Fin 9)
  | degree (x : Bits)
  | pairUpper (x y : Bits)
  | pairLower (x y : Bits)
  | shellLower (x : Bits)
  | forcedEdge (x : Bits) (i : Fin 9)
  | agreementEdge (x y : Bits) (i : Fin 9)
  | agreement (x : Bits) (i : Fin 9) (factor : ℤ)

private def Row.terms : Row → List Term
  | .size => cubeTerms (allowed deficit) (fun x => single x 1)
  | .parity => cubeTerms (fun x => (allowed deficit) x && cubeParity (cube x)) (fun x => single x 1)
  | .half i => cubeTerms (fun x => (allowed deficit) x && cube x i) (fun x => single x 1)
  | .direction i => cubeTerms (fun x => (allowed deficit) x && !(cube x i) && (allowed deficit) (bitFlip x i))
      (fun x => pair x (bitFlip x i) 1)
  | .degree x => single x (-3) :: termsOf (fun i => (allowed deficit) (bitFlip x i))
      (fun i => pair x (bitFlip x i) 1)
  | .pairUpper x y => [pair x y 1, single x (-1)]
  | .pairLower x y => [single x 1, single y 1, pair x y (-1)]
  | .shellLower x => single x (2 * weight deficit x + 12 - ∑ i, deficit i) ::
      cubeTerms (fun y => decide (hammingDist (cube x) (cube y) = 7) && allowedFar deficit x y)
        (fun y => pair x y (-1))
  | .forcedEdge x i => [single x 1, pair x (bitFlip x i) (-1)]
  | .agreementEdge x y i => [pair x y 1, pair x (bitFlip x i) 1, single x (-1)]
  | .agreement x i factor => single x (-factor) ::
      (if (allowed deficit) (bitFlip x i) then [pair x (bitFlip x i) factor] else []) ++
      cubeTerms (fun y => farAgreement x y i && allowedFar deficit x y)
        (fun y => pair x y (if factor = 4 then 1 else -1))

private def Row.bound : Row → ℤ
  | .size => 66
  | .parity => 33
  | .half i => 33 - 2 * deficit i
  | .direction _ => 11
  | .pairLower .. => 1
  | _ => 0

-- Count the four joint bit patterns in each of the six possible deficit values.
private def orderedKey (x y : Bits) : List ℕ :=
  [0, 1, 2, 3, 4, 5].flatMap fun d =>
    let count (a b : Bool) := (univ.filter fun i : Fin 9 =>
      deficit i = d ∧ cube x i = a ∧ cube y i = b).card
    [count false false, count false true, count true false, count true true]

private abbrev Key := Bool × List ℕ

private def orbitKey : Variable → Key
  | .inl x => (false, orderedKey deficit x x)
  | .inr (x, y) =>
    -- Pair membership is symmetric, so either orientation can represent the orbit.
    let a := orderedKey deficit x y
    let b := orderedKey deficit y x
    (true, if a.lex b then a else b)

variable (certificate : List (Row × ℤ × ℤ))

private def combined : List Term := certificate.flatMap fun (row, sign, w) =>
  (Row.terms deficit row).map fun (v, a) => (v, w * sign * a)

private def upper : ℤ := (certificate.map fun (row, sign, w) => w * sign * (Row.bound deficit row)).sum

private def keys (terms : List (Key × ℤ)) : Finset Key := (terms.map Prod.fst).toFinset
private def coefficient (terms : List (Key × ℤ)) (k : Key) : ℤ :=
  (terms.map fun (j, a) => if j = k then a else 0).sum

private def lower (terms : List (Key × ℤ)) : ℤ :=
  ∑ k ∈ keys terms, min 0 (coefficient terms k)

private def keyedTerms : List (Key × ℤ) := (combined deficit certificate).map fun (v, a) => (orbitKey deficit v, a)

noncomputable section

attribute [local instance] Classical.propDecidable

private abbrev Perm := deficitPermutations deficit
private noncomputable instance : Fintype (Perm deficit) := Fintype.ofFinite (Perm deficit)

private def value (C : Finset Vertex) : Variable → ℤ
  | .inl x => cubeMembership C (cube x)
  | .inr (x, y) => cubePairMembership C (cube x) (cube y)

private def transportedValue (C : Finset Vertex) (p : Perm deficit) : Variable → ℤ
  | .inl x => cubeMembership C (p • cube x)
  | .inr (x, y) => cubePairMembership C (p • cube x) (p • cube y)

private def average (C : Finset Vertex) (v : Variable) : ℤ :=
  ∑ p : Perm deficit, transportedValue deficit C p v

variable (hrange : ∀ i, 0 ≤ deficit i ∧ deficit i ≤ 5)

include hrange in
private lemma orderedKey_orbit {x y u v : Bits} (h : orderedKey deficit x y = orderedKey deficit u v) :
    ∃ p : Perm deficit, p • (cube x, cube y) = (cube u, cube v) := by
  apply joint_bit_counts_same_orbit
  intro d a b
  by_cases hd : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5
  · simp only [orderedKey, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.cons.injEq, and_true] at h
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> cases a <;> cases b <;> tauto
  · have hn (i : Fin 9) : deficit i ≠ d := by
      intro hi
      have := hrange i
      omega
    simp [hn]

include hrange in
private lemma average_pair_ordered (C : Finset Vertex) {x y u v : Bits}
    (h : orderedKey deficit x y = orderedKey deficit u v) :
    average deficit C (.inr (x, y)) = average deficit C (.inr (u, v)) := by
  obtain ⟨p, hp⟩ := orderedKey_orbit deficit hrange h
  change (∑ q : Perm deficit, (fun t : Vertex × Vertex => cubePairMembership C t.1 t.2)
    (q • (cube x, cube y))) = ∑ q : Perm deficit, (fun t : Vertex × Vertex => cubePairMembership C t.1 t.2)
      (q • (cube u, cube v))
  rw [← hp]
  exact (orbit_sum_invariant (fun t : Vertex × Vertex => cubePairMembership C t.1 t.2)
    p (cube x, cube y)).symm

private lemma average_swap (C : Finset Vertex) (x y : Bits) :
    average deficit C (.inr (x, y)) = average deficit C (.inr (y, x)) := by
  simp only [average, transportedValue, cubePairMembership, mul_comm]

include hrange in
private lemma average_orbit (C : Finset Vertex) {s t : Variable}
    (h : (orbitKey deficit) s = orbitKey deficit t) : average deficit C s = average deficit C t := by
  rcases s with x | ⟨x, y⟩ <;> rcases t with u | ⟨u, v⟩
  · have hk : orderedKey deficit x x = orderedKey deficit u u := congrArg Prod.snd h
    obtain ⟨p, hp⟩ := orderedKey_orbit deficit hrange hk
    have he : p • cube x = cube u := congrArg Prod.fst hp
    change (∑ q : Perm deficit, cubeMembership C (q • cube x)) =
      ∑ q : Perm deficit, cubeMembership C (q • cube u)
    rw [← he]
    exact (orbit_sum_invariant (cubeMembership C) p (cube x)).symm
  · cases (congrArg Prod.fst h : false = true)
  · cases (congrArg Prod.fst h : true = false)
  · have hk := congrArg Prod.snd h
    simp only [orbitKey] at hk
    split at hk <;> split at hk
    · exact average_pair_ordered deficit hrange C hk
    · exact (average_pair_ordered deficit hrange C hk).trans (average_swap deficit C v u)
    · exact (average_swap deficit C x y).trans (average_pair_ordered deficit hrange C hk)
    · exact (average_swap deficit C x y).trans
        ((average_pair_ordered deficit hrange C hk).trans (average_swap deficit C v u))

private lemma average_bounds (C : Finset Vertex) (v : Variable) :
    0 ≤ average deficit C v ∧ average deficit C v ≤ Fintype.card (Perm deficit) := by
  have h (p : Perm deficit) : 0 ≤ transportedValue deficit C p v ∧ transportedValue deficit C p v ≤ 1 := by
    classical
    rcases v with x | ⟨x, y⟩
    · by_cases hx : p • cube x ∈ C <;> simp [transportedValue, cubeMembership, hx]
    · by_cases hx : p • cube x ∈ C <;> by_cases hy : p • cube y ∈ C <;>
        simp [transportedValue, cubePairMembership, cubeMembership, hx, hy]
  refine ⟨sum_nonneg (fun p _ => (h p).1), ?_⟩
  simpa [average] using sum_le_sum (s := (univ : Finset (Perm deficit))) (fun p _ => (h p).2)

private def evalTerms (terms : List Term) (z : Variable → ℤ) : ℤ :=
  (terms.map fun (v, a) => a * z v).sum

private lemma eval_transport_sum (C : Finset Vertex) (terms : List Term) :
    evalTerms terms (average deficit C) = ∑ p : Perm deficit, evalTerms terms (transportedValue deficit C p) := by
  induction terms with
  | nil => simp [evalTerms]
  | cons t ts ih =>
    rcases t with ⟨v, a⟩
    simp only [evalTerms, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, average, mul_sum, sum_add_distrib]

private lemma eval_combined (z : Variable → ℤ)
    (h : ∀ t ∈ certificate, t.2.1 * evalTerms (Row.terms deficit t.1) z ≤ t.2.1 * (Row.bound deficit t.1))
    (hw : ∀ t ∈ certificate, 0 ≤ t.2.2) :
    evalTerms (combined deficit certificate) z ≤ upper deficit certificate := by
  unfold combined upper
  suffices ∀ rows : List (Row × ℤ × ℤ), (∀ t ∈ rows, t ∈ certificate) →
      evalTerms (rows.flatMap fun (r, s, w) => (Row.terms deficit r).map fun (v, a) => (v, w * s * a)) z ≤
        (rows.map fun (r, s, w) => w * s * (Row.bound deficit r)).sum from this _ (fun _ ht => ht)
  intro rows
  induction rows with
  | nil => simp [evalTerms]
  | cons t ts ih =>
    rcases t with ⟨r, s, w⟩
    intro hsub
    have ht := hsub (r, s, w) (by simp)
    have hw' := mul_le_mul_of_nonneg_left (h _ ht) (hw _ ht)
    have hts := ih (fun t ht => hsub t (List.mem_cons_of_mem _ ht))
    simp only [List.flatMap_cons, List.map_cons, List.sum_cons, evalTerms, List.map_append,
      List.sum_append, List.map_map, Function.comp_def] at hts ⊢
    simp only [mul_assoc, List.sum_map_mul_left] at *
    exact add_le_add hw' hts

private lemma eval_grouped (terms : List (Key × ℤ)) (f : Key → ℤ) (K : Finset Key)
    (hK : ∀ k a, (k, a) ∈ terms → k ∈ K) :
    (terms.map fun (k, a) => a * f k).sum = ∑ k ∈ K, coefficient terms k * f k := by
  induction terms with
  | nil => simp [coefficient]
  | cons t ts ih =>
    rcases t with ⟨j, a⟩
    have hj := hK j a (by simp)
    simp only [List.map_cons, List.sum_cons]
    rw [ih (fun k b hb => hK k b (List.mem_cons_of_mem _ hb))]
    simp only [coefficient, List.map_cons, List.sum_cons, add_mul, sum_add_distrib]
    congr 1
    rw [sum_eq_single j]
    · simp
    · intro k _ h
      simp [Ne.symm h]
    · exact fun h => (h hj).elim

include hrange in
private lemma lower_bound (C : Finset Vertex) :
    (Fintype.card (Perm deficit) : ℤ) * lower (keyedTerms deficit certificate) ≤ evalTerms (combined deficit certificate) (average deficit C) := by
  classical
  let f (k : Key) := if h : ∃ v, (orbitKey deficit) v = k then average deficit C (Classical.choose h) else 0
  have hf (v : Variable) : f (orbitKey deficit v) = average deficit C v := by
    have h : ∃ u, orbitKey deficit u = (orbitKey deficit) v := ⟨v, rfl⟩
    rw [show f (orbitKey deficit v) = average deficit C (Classical.choose h) from dite_eq_left h]
    exact average_orbit deficit hrange C (Classical.choose_spec h)
  have hbox (k : Key) : 0 ≤ f k ∧ f k ≤ Fintype.card (Perm deficit) := by
    dsimp only [f]
    split
    · exact average_bounds deficit C _
    · simp
  have hgroup := eval_grouped (keyedTerms deficit certificate) f (keys (keyedTerms deficit certificate)) (fun k a h => by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(k, a), h, rfl⟩))
  simp only [keyedTerms, List.map_map, Function.comp_def, hf] at hgroup
  rw [show evalTerms (combined deficit certificate) (average deficit C) = _ from hgroup, lower, mul_sum]
  apply sum_le_sum
  intro k _
  let a := coefficient (keyedTerms deficit certificate) k
  change _ * min 0 a ≤ a * f k
  by_cases ha : 0 ≤ a
  · simpa [min_eq_left ha] using mul_nonneg ha (hbox k).1
  · rw [min_eq_right (le_of_not_ge ha), mul_comm]
    exact mul_le_mul_of_nonpos_left (hbox k).2 (le_of_not_ge ha)


private lemma eval_termsOf {n : ℕ} (p : Fin n → Bool) (t : Fin n → Term)
    (z : Variable → ℤ) :
    evalTerms (termsOf p t) z =
      ∑ i ∈ univ.filter (fun i => p i), (t i).2 * z (t i).1 := by
  rw [sum_filter, ← List.sum_ofFn]
  have h (l : List (Fin n)) :
      evalTerms ((l.filter p).map t) z =
        (l.map fun i => if p i then (t i).2 * z (t i).1 else 0).sum := by
    induction l with
    | nil => rfl
    | cons i l ih =>
      simp only [evalTerms, List.map_map] at ih ⊢
      cases hp : p i <;> simp [hp, ih]
  simpa only [termsOf, List.finRange, List.map_ofFn, Function.comp_def] using h (List.finRange n)

private def indexCube : Fin (2 ^ 9) ≃ Vertex :=
  (show Fin (2 ^ 9) ≃ Bits from
    { toFun := @BitVec.ofFin 9
      invFun := BitVec.toFin
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans cube

private lemma eval_cubeTerms (p : Bits → Bool) (t : Bits → Term) (z : Variable → ℤ) :
    evalTerms (cubeTerms p t) z =
      ∑ x ∈ univ.filter (fun x => p (cube.symm x)),
        (t (cube.symm x)).2 * z (t (cube.symm x)).1 := by
  rw [cubeTerms, eval_termsOf, sum_filter, sum_filter, ← indexCube.sum_comp]
  simp [indexCube]

private lemma sum_filter_weaken {I : Type*} [Fintype I] (P Q' : I → Prop)
    [DecidablePred P] [DecidablePred Q'] (f : I → ℤ)
    (himp : ∀ i, P i → Q' i) (hzero : ∀ i, Q' i → ¬ P i → f i = 0) :
    ∑ i ∈ univ.filter P, f i = ∑ i ∈ univ.filter Q', f i := by
  rw [sum_filter, sum_filter]
  apply sum_congr rfl
  intro i _
  by_cases hP : P i
  · simp [hP, himp i hP]
  by_cases hQ : Q' i
  · simp [hP, hQ, hzero i hQ hP]
  · simp [hP, hQ]

private lemma cube_bitFlip (x : Bits) (i : Fin 9) : cube (bitFlip x i) = flip (cube x) i :=
  cubeBitVec_xor_single x i

private lemma half_eq_rows {C : Finset Vertex} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33) :
    (∑ x : Vertex, cubeMembership C x) = 66 ∧
    (∀ b, (∑ x ∈ univ.filter (fun x => cubeParity x = b), cubeMembership C x) = 33) ∧
    (∀ i, (∑ x ∈ univ.filter (fun x => x i = true), cubeMembership C x) = 33 - 2 * deficit i) ∧
    ∀ i, (∑ x ∈ univ.filter (fun x => x i = false), cubePairMembership C x (flip x i)) = 11 :=
  cube_lifted_cardinality_rows hC (cubic_parity_half_card hC hreg) hhalf (fun i => by
    have h := direction_edge_count (d := 3) C hreg hb i
    omega)

private def Row.Valid : Row → Prop
  | .agreementEdge x y i => farAgreement x y i = true
  | .forcedEdge x i => 2 * weight deficit x + 12 = (∑ j, deficit j) + 8 ∧
      cube x i = true ∧ 2 ≤ deficit i
  | .agreement x _ k => k = 4 ∨ (k = -2 ∧ 2 * weight deficit x + 12 = (∑ i, deficit i) + 8)
  | _ => True

private instance Row.validDecidable (row : Row) : Decidable (Row.Valid deficit row) := by
  cases row <;> unfold Row.Valid <;> infer_instance

private def Row.SignAllowed (sign : ℤ) : Row → Prop
  | .pairUpper .. | .pairLower .. | .shellLower .. | .forcedEdge ..
  | .agreementEdge .. | .agreement .. => sign = 1
  | _ => True

private instance Row.signAllowedDecidable (sign : ℤ) (row : Row) :
    Decidable (Row.SignAllowed sign row) := by
  cases row <;> unfold Row.SignAllowed <;> infer_instance

include hrange in
private lemma support_rows {C : Finset Vertex} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33)
    (row : Row) (hrow : Row.Valid deficit row) (sign : ℤ)
    (hineq : Row.SignAllowed sign row) :
    sign * evalTerms (Row.terms deficit row) (value C) ≤ sign * (Row.bound deficit row) := by
  classical
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hC hreg hb
  have hshell (x : Vertex) (hx : x ∈ C) :
      (shell C x 7).card ≤ 8 ∧
      2 * (∑ i, if x i then deficit i else 0) + 12 ≤ (∑ i, deficit i) + (shell C x 7).card :=
    ⟨sixty_six_distance_seven_le_eight hC hreg hb hd hx,
      coordinate_profile_weight_bound hC hreg hb (fun _ => true) deficit hhalf hx⟩
  have hallow (x : Bits) (hx : cube x ∈ C) : (allowed deficit) x = true := by
    obtain ⟨hc, hw⟩ := hshell (cube x) hx
    change 2 * weight deficit x + 12 ≤ (∑ i, deficit i) + ((shell C (cube x) 7).card : ℤ) at hw
    exact decide_eq_true (show 2 * weight deficit x + 12 ≤ (∑ i, deficit i) + 8 by omega)
  have hz (x : Bits) (hx : ¬ ((allowed deficit) x = true)) : cubeMembership C (cube x) = 0 := by
    have hn : cube x ∉ C := fun h => hx (hallow x h)
    simp [cubeMembership, hn]
  have hzPair (x y : Bits) (hx : ¬ ((allowed deficit) x = true ∧ (allowed deficit) y = true)) :
      cubePairMembership C (cube x) (cube y) = 0 := by
    by_cases hx' : (allowed deficit) x = true
    · simp [cubePairMembership, hz y (fun hy => hx ⟨hx', hy⟩)]
    · simp [cubePairMembership, hz x hx']
  have hzFar (x y : Bits) (h : hammingDist (cube x) (cube y) = 7)
      (hn : ¬ allowedFar deficit x y = true) : cubePairMembership C (cube x) (cube y) = 0 := by
    by_cases hx : cube x ∈ C <;> by_cases hy : cube y ∈ C
    · exfalso
      apply hn
      simp only [allowedFar, Bool.and_eq_true, hallow y hy, true_and, List.all_eq_true]
      intro j _
      by_cases hj : cube x j = true
      · by_cases hej : cube y j = cube x j
        · have hm := distance_seven_agreement_excludes_minority hC hreg hb hd (fun _ => true)
            deficit hrange hhalf hx hy h hej.symm hj
          simp [hj, hej, show ¬ 1 < deficit j from not_lt.mpr hm]
        · have hfalse : cube y j = false :=
            Bool.eq_false_of_not_eq_true (fun htrue => hej (htrue.trans hj.symm))
          simp [hfalse]
      · have hj' : cube x j = false := Bool.eq_false_of_not_eq_true hj
        simp [hj']
    all_goals simp [cubePairMembership, cubeMembership, hx, hy]
  obtain ⟨hsize, hparity, hhalf', hdir⟩ := half_eq_rows deficit hC hreg hb hhalf
  have hsingle (p : Vertex → Bool) :
      evalTerms (cubeTerms (fun x => (allowed deficit) x && p (cube x)) (fun x => single x 1)) (value C) =
      ∑ x ∈ univ.filter (fun x => p x), cubeMembership C x := by
    simp only [eval_cubeTerms, single, value, Equiv.apply_symm_apply, one_mul, Bool.and_eq_true]
    apply sum_filter_weaken
    · exact fun _ h => h.2
    · intro x h hx
      simpa using hz (cube.symm x) (fun ha => hx ⟨ha, h⟩)
  have hs : evalTerms (Row.terms deficit Row.size) (value C) = 66 := by
    simpa [Row.terms] using (hsingle (fun _ => true)).trans (by simpa using hsize)
  have hp : evalTerms (Row.terms deficit Row.parity) (value C) = 33 := (hsingle cubeParity).trans (hparity true)
  have hh (i : Fin 9) : evalTerms (Row.terms deficit (Row.half i)) (value C) = (Row.bound deficit (Row.half i)) :=
    (hsingle (fun x => x i)).trans (hhalf' i)
  have he (i : Fin 9) : evalTerms (Row.terms deficit (Row.direction i)) (value C) = 11 := by
    rw [Row.terms, eval_cubeTerms, ← hdir i]
    simp only [pair, value, cube_bitFlip, Equiv.apply_symm_apply, one_mul, Bool.and_eq_true,
      Bool.not_eq_true']
    apply sum_filter_weaken
    · exact fun _ h => h.1.2
    · intro x hx hf
      simpa only [cube_bitFlip, Equiv.apply_symm_apply] using
        hzPair (cube.symm x) (bitFlip (cube.symm x) i) (fun h => hf ⟨⟨h.1, hx⟩, h.2⟩)
  have hn (x : Bits) (i : Fin 9) (h : ¬ (allowed deficit) (bitFlip x i) = true) :
      cubePairMembership C (cube x) (flip (cube x) i) = 0 := by
    simpa only [cube_bitFlip] using hzPair x (bitFlip x i) (fun h' => h h'.2)
  have hc (x : Bits) : evalTerms (Row.terms deficit (Row.degree x)) (value C) = 0 := by
    simp only [Row.terms, evalTerms, List.map_cons, List.sum_cons, single, value]
    change -3 * cubeMembership C (cube x) +
      evalTerms (termsOf _ _) (value C) = 0
    simp only [eval_termsOf, pair, value, cube_bitFlip, one_mul]
    have h := cube_lifted_incidence_rows hreg hshell (cube x)
    rw [show (∑ i ∈ univ.filter (fun i => allowed deficit (bitFlip x i)), _) =
        ∑ i, cubePairMembership C (cube x) (flip (cube x) i) from by
      rw [← filter_true_of_mem (s := (univ : Finset (Fin 9))) (p := fun _ => True)
        (fun _ _ => trivial)]
      exact sum_filter_weaken _ _ _ (fun _ _ => trivial) (fun i _ hi => hn x i hi)]
    linarith only [h.1]
  have hagree (x : Bits) (i : Fin 9) (k : ℤ) :
      evalTerms (Row.terms deficit (Row.agreement x i k)) (value C) =
        (if k = 4 then 1 else -1) *
          (∑ y ∈ univ.filter (fun y => hammingDist (cube x) y = 7 ∧ cube x i = y i),
            cubePairMembership C (cube x) y) -
        k * (cubeMembership C (cube x) - cubePairMembership C (cube x) (flip (cube x) i)) := by
    have hfar :
        evalTerms (cubeTerms (fun y => farAgreement x y i && allowedFar deficit x y)
          (fun y => pair x y (if k = 4 then 1 else -1))) (value C) =
        (if k = 4 then 1 else -1) *
          ∑ y ∈ univ.filter (fun y => hammingDist (cube x) y = 7 ∧ cube x i = y i),
            cubePairMembership C (cube x) y := by
      rw [eval_cubeTerms, mul_sum]
      simp only [pair, value, Equiv.apply_symm_apply, Bool.and_eq_true]
      apply sum_filter_weaken
      · intro y hy
        simpa only [farAgreement, decide_eq_true_eq, Equiv.apply_symm_apply] using hy.1
      · intro y hy hny
        have hdy : farAgreement x (cube.symm y) i = true := by simpa [farAgreement] using hy
        rw [show cubePairMembership C (cube x) y = 0 by
          simpa only [Equiv.apply_symm_apply] using
            hzFar x (cube.symm y) (of_decide_eq_true hdy).1
              (fun ha => hny ⟨hdy, ha⟩), mul_zero]
    have hnear : evalTerms (if (allowed deficit) (bitFlip x i) then
        [pair x (bitFlip x i) k] else []) (value C) =
        k * cubePairMembership C (cube x) (flip (cube x) i) := by
      split
      · simp [evalTerms, pair, value, cube_bitFlip]
      · simp [evalTerms, hn x i (by assumption)]
    simp only [Row.terms, evalTerms, List.map_cons, List.sum_cons, single, value, List.map_append,
      List.sum_append]
    simp only [evalTerms, value] at hnear hfar
    rw [hnear, hfar]
    ring
  have hcap (x : Bits) (i : Fin 9) : evalTerms (Row.terms deficit (Row.agreement x i 4)) (value C) ≤ 0 := by
    have h := (cube_lifted_agreement_capacity hreg hb hd (cube x) i).1
    rw [hagree]
    simpa using sub_nonpos.mpr h
  have hfloor (x : Bits) (i : Fin 9) (hx : 2 * weight deficit x + 12 = (∑ i, deficit i) + 8) :
      evalTerms (Row.terms deficit (Row.agreement x i (-2))) (value C) ≤ 0 := by
    rw [hagree]
    have h := (cube_lifted_agreement_capacity hreg hb hd (cube x) i).2
    by_cases hm : cube x ∈ C
    · obtain ⟨hc', hw⟩ := hshell (cube x) hm
      change 2 * weight deficit x + 12 ≤ (∑ i, deficit i) + ((shell C (cube x) 7).card : ℤ) at hw
      rw [hx] at hw
      have h8 : (shell C (cube x) 7).card = 8 := by omega
      have hf := h h8
      norm_num
      linarith only [hf]
    · simp [cubePairMembership, cubeMembership, hm]
  have hpair (x y : Bits) :
      evalTerms (Row.terms deficit (Row.pairUpper x y)) (value C) ≤ 0 := by
    have h := (cube_lifted_pair_rows C (cube x) (cube y)).1
    simp [Row.terms, evalTerms, single, pair, value]
    linarith only [h]
  have hpairLower (x y : Bits) :
      evalTerms (Row.terms deficit (Row.pairLower x y)) (value C) ≤ 1 := by
    have h := (cube_lifted_pair_rows C (cube x) (cube y)).2.2
    simp [Row.terms, evalTerms, single, pair, value]
    linarith only [h]
  have hshellLower (x : Bits) :
      evalTerms (Row.terms deficit (Row.shellLower x)) (value C) ≤ 0 := by
    have hfar :
        evalTerms (cubeTerms
          (fun y => decide (hammingDist (cube x) (cube y) = 7) && allowedFar deficit x y)
          (fun y => pair x y (-1))) (value C) =
        (-1) * ∑ y ∈ univ.filter (fun y => hammingDist (cube x) y = 7),
          cubePairMembership C (cube x) y := by
      rw [eval_cubeTerms, mul_sum]
      simp only [pair, value, Equiv.apply_symm_apply]
      apply sum_filter_weaken
      · intro y hy
        simpa only [Bool.and_eq_true, decide_eq_true_eq, Equiv.apply_symm_apply] using
          (Bool.and_eq_true_iff.mp hy).1
      · intro y hy hny
        have hdy : hammingDist (cube x) (cube (cube.symm y)) = 7 := by simpa using hy
        have hzero := hzFar x (cube.symm y) hdy
          (fun ha => hny (Bool.and_eq_true_iff.mpr ⟨decide_eq_true hy, ha⟩))
        simpa only [Equiv.apply_symm_apply] using (show (-1 : ℤ) *
          cubePairMembership C (cube x) (cube (cube.symm y)) = 0 by rw [hzero, mul_zero])
    have h := (cube_lifted_incidence_rows hreg hshell (cube x)).2.1
    change (2 * weight deficit x + 12 - ∑ i, deficit i) * cubeMembership C (cube x) ≤ _ at h
    simp only [Row.terms, evalTerms, List.map_cons, List.sum_cons, single, value]
    simp only [evalTerms, value] at hfar
    rw [hfar]
    linarith only [h]
  have hedge (x y : Bits) (i : Fin 9) (h : farAgreement x y i = true) :
      evalTerms (Row.terms deficit (Row.agreementEdge x y i)) (value C) ≤ 0 := by
    have hf : hammingDist (cube x) (cube y) = 7 ∧ cube x i = cube y i := of_decide_eq_true h
    have he' := cube_lifted_agreement_row hd hf.1 hf.2
    simp [Row.terms, evalTerms, single, pair, value, cube_bitFlip]
    linarith only [he']
  have hforced (x : Bits) (i : Fin 9) (hvalid : Row.Valid deficit (.forcedEdge x i)) :
      evalTerms (Row.terms deficit (Row.forcedEdge x i)) (value C) ≤ 0 := by
    obtain ⟨hw, hbit, hmin⟩ := hvalid
    by_cases hx : cube x ∈ C
    · obtain ⟨hc, h⟩ := hshell _ hx
      change 2 * weight deficit x + 12 ≤ (∑ j, deficit j) + ((shell C (cube x) 7).card : ℤ) at h
      have h8 : (shell C (cube x) 7).card = 8 := by rw [hw] at h; omega
      have hf := eight_partners_force_minority_directions_used hC hreg hb hd
        (fun _ => true) deficit hhalf (fun j => (hrange j).1) hx h8 hbit hmin
      simp [Row.terms, evalTerms, single, pair, value, cube_bitFlip,
        cubePairMembership, cubeMembership, hx, hf]
    · simp [Row.terms, evalTerms, single, pair, value, cubePairMembership, cubeMembership, hx]
  unfold Row.SignAllowed at hineq
  cases row with
  | size => simp [hs, Row.bound]
  | parity => simp [hp, Row.bound]
  | half i => rw [hh]
  | direction i => simp [he, Row.bound]
  | degree x => simp [hc, Row.bound]
  | pairUpper x y => simpa only [hineq, one_mul, Row.bound] using hpair x y
  | pairLower x y => simpa only [hineq, one_mul, Row.bound] using hpairLower x y
  | shellLower x => simpa only [hineq, one_mul, Row.bound] using hshellLower x
  | forcedEdge x i => simpa only [hineq, one_mul, Row.bound] using hforced x i hrow
  | agreementEdge x y i => simpa only [hineq, one_mul, Row.bound] using hedge x y i hrow
  | agreement x i k =>
    rcases hrow with h | ⟨h, hw⟩
    · subst k
      simpa only [hineq, one_mul, Row.bound] using hcap x i
    · subst k
      simpa only [hineq, one_mul, Row.bound] using hfloor x i hw

include hrange in
private lemma certificate_contradiction {C : Finset Vertex} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hh : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33)
    (hw : ∀ t ∈ certificate, 0 ≤ t.2.2 ∧ Row.Valid deficit t.1 ∧ Row.SignAllowed t.2.1 t.1)
    (hgap : (upper deficit certificate) < lower (keyedTerms deficit certificate)) : False := by
  have hrows (p : Perm deficit) : evalTerms (combined deficit certificate) (transportedValue deficit C p) ≤ upper deficit certificate := by
    obtain ⟨T, hT, hregT, hbT, hhT, hp⟩ := transport_lifted_cube_support hC hreg hb hh p
    have he : transportedValue deficit C p = value T := by
      funext v
      rcases v with x | ⟨x, y⟩
      · exact (hp (cube x)).symm
      · simp only [transportedValue, value, cubePairMembership, hp]
    rw [he]
    exact eval_combined deficit certificate (value T)
      (fun t ht => support_rows deficit hrange hT hregT hbT hhT t.1 (hw t ht).2.1 t.2.1
        (hw t ht).2.2) (fun t ht => (hw t ht).1)
  have hu : evalTerms (combined deficit certificate) (average deficit C) ≤ (Fintype.card (Perm deficit) : ℤ) * upper deficit certificate := by
    rw [eval_transport_sum]
    simpa only [sum_const, card_univ, nsmul_eq_mul] using
      sum_le_sum (s := (univ : Finset (Perm deficit))) (fun p _ => hrows p)
  have h := (lower_bound deficit certificate hrange C).trans hu
  have hd : 0 < (Fintype.card (Perm deficit) : ℤ) := by exact_mod_cast Fintype.card_pos
  exact (not_lt_of_ge h) (mul_lt_mul_of_pos_left hgap hd)

end
end

attribute [local instance] Classical.propDecidable

private def deficit114555555 : Fin 9 → ℤ := ![1, 1, 4, 5, 5, 5, 5, 5, 5]

-- Each entry gives the row, its sign, and its nonnegative multiplier.
private def certificate114555555 : List (Row × ℤ × ℤ) :=
  [(.pairUpper 450 56, 1, 1000), (.agreementEdge 56 450 0, 1, 2001),
   (.size, 1, 1550), (.parity, 1, 113), (.direction 2, 1, 338), (.direction 3, 1, 1525),
   (.degree 12, 1, 500), (.degree 13, 1, 1000), (.degree 15, 1, 50),
   (.degree 31, 1, 5064), (.degree 57, 1, 8169),
   (.half 0, -1, 225), (.half 2, -1, 525), (.half 3, -1, 4651),
   (.degree 27, -1, 3376), (.degree 28, -1, 5064), (.degree 29, -1, 10128),
   (.degree 56, -1, 5085),
   (.agreement 27 0 4, 1, 1688), (.agreement 28 0 4, 1, 2251),
   (.agreement 29 0 4, 1, 2813),
   (.agreement 31 2 (-2), 1, 3376), (.agreement 31 3 (-2), 1, 9002),
   (.agreement 57 1 (-2), 1, 3001), (.agreement 57 3 (-2), 1, 27507)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
-- The kernel reduces the sparse rows and their orbit coefficients.
/-- No Huang-balanced induced cubic 66-point support has normalized deficit
profile `[1,1,4,5,5,5,5,5,5]` on its true coordinate halves. -/
theorem q9_sixty_six_excludes_114555555 {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i : Fin 9, ((C.filter fun x => x i = true).card : ℤ) +
      2 * (![1, 1, 4, 5, 5, 5, 5, 5, 5] : Fin 9 → ℤ) i = 33) : False := by
  apply certificate_contradiction deficit114555555 certificate114555555
    (by decide +kernel) hC hreg hb hhalf
  · simp only [certificate114555555, List.forall_mem_cons]
    repeat' apply And.intro
    all_goals first | exact List.forall_mem_nil _ | decide +kernel
  · decide +kernel

#print axioms q9_sixty_six_excludes_114555555


private def deficit014455555 : Fin 9 → ℤ := ![0, 1, 4, 4, 5, 5, 5, 5, 5]

private def certificate014455555 : List (Row × ℤ × ℤ) :=
  [(.pairLower 48 49, 1, 1495), (.agreementEdge 22 449 5, 1, 227),
   (.agreementEdge 23 448 5, 1, 227), (.agreementEdge 385 30 5, 1, 1495),
   (.agreementEdge 384 31 5, 1, 1495), (.agreementEdge 50 449 2, 1, 57),
   (.agreementEdge 51 448 2, 1, 57), (.agreementEdge 52 394 0, 1, 4838),
   (.agreementEdge 52 449 1, 1, 738), (.agreementEdge 53 395 0, 1, 4838),
   (.agreementEdge 53 448 1, 1, 738), (.agreementEdge 448 54 0, 1, 1726),
   (.agreementEdge 449 55 0, 1, 1726), (.shellLower 30, 1, 249),
   (.shellLower 31, 1, 249), (.shellLower 112, 1, 57),
   (.shellLower 113, 1, 57), (.size, 1, 1818),
   (.direction 0, 1, 75), (.direction 2, 1, 484),
   (.direction 4, 1, 906), (.degree 12, 1, 159),
   (.degree 13, 1, 159), (.degree 14, 1, 67),
   (.degree 15, 1, 67), (.degree 20, 1, 980),
   (.degree 21, 1, 980), (.degree 22, 1, 175),
   (.degree 23, 1, 175), (.degree 48, 1, 374),
   (.degree 49, 1, 374), (.degree 54, 1, 4847),
   (.degree 55, 1, 4847), (.half 1, -1, 219),
   (.half 2, -1, 1342), (.half 4, -1, 4264),
   (.degree 28, -1, 1699), (.degree 29, -1, 1699),
   (.degree 30, -1, 1297), (.degree 31, -1, 1297),
   (.degree 50, -1, 374), (.degree 51, -1, 374),
   (.degree 52, -1, 5585), (.degree 53, -1, 5585),
   (.degree 112, -1, 1514), (.degree 113, -1, 2685),
   (.agreement 14 4 4, 1, 14), (.agreement 15 4 4, 1, 14),
   (.agreement 28 0 4, 1, 378), (.agreement 28 1 4, 1, 425),
   (.agreement 29 0 4, 1, 378), (.agreement 29 1 4, 1, 425),
   (.agreement 30 0 4, 1, 278), (.agreement 30 1 4, 1, 324),
   (.agreement 31 0 4, 1, 278), (.agreement 31 1 4, 1, 324),
   (.agreement 54 0 (-2), 1, 1613), (.agreement 54 2 (-2), 1, 4497),
   (.agreement 54 4 (-2), 1, 8937), (.agreement 55 0 (-2), 1, 1613),
   (.agreement 55 2 (-2), 1, 4497), (.agreement 55 4 (-2), 1, 8937),
   (.agreement 112 1 (-2), 1, 312), (.agreement 112 4 (-2), 1, 1756),
   (.agreement 113 1 (-2), 1, 312)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
-- The kernel reduces the 65 sparse rows and combines their orbit coefficients.
/-- The normalized deficit profile `[0,1,4,4,5,5,5,5,5]` is impossible. -/
theorem q9_sixty_six_excludes_014455555 {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i : Fin 9, ((C.filter fun x => x i = true).card : ℤ) +
      2 * (![0, 1, 4, 4, 5, 5, 5, 5, 5] : Fin 9 → ℤ) i = 33) : False := by
  apply certificate_contradiction deficit014455555 certificate014455555
    (by decide +kernel) hC hreg hb hhalf
  · simp only [certificate014455555, List.forall_mem_cons]
    repeat' apply And.intro
    all_goals first | exact List.forall_mem_nil _ | decide +kernel
  · decide +kernel

#print axioms q9_sixty_six_excludes_014455555


private def deficit004445555 : Fin 9 → ℤ := ![0, 0, 4, 4, 4, 5, 5, 5, 5]

private def certificate004445555 : List (Row × ℤ × ℤ) :=
  [(.pairUpper 28 29, 1, 53), (.pairUpper 29 28, 1, 53),
   (.pairUpper 29 31, 1, 53), (.pairUpper 31 29, 1, 53),
   (.agreementEdge 12 403 5, 1, 35), (.agreementEdge 13 402 5, 1, 70),
   (.agreementEdge 15 400 5, 1, 35), (.agreementEdge 36 403 6, 1, 140),
   (.agreementEdge 36 283 6, 1, 140), (.agreementEdge 37 402 6, 1, 280),
   (.agreementEdge 37 282 6, 1, 280), (.agreementEdge 39 400 6, 1, 140),
   (.agreementEdge 39 280 6, 1, 140), (.agreementEdge 44 402 0, 1, 420),
   (.agreementEdge 387 44 4, 1, 140), (.agreementEdge 45 403 0, 1, 420),
   (.agreementEdge 45 400 1, 1, 420), (.agreementEdge 386 45 4, 1, 280),
   (.agreementEdge 47 401 0, 1, 420), (.agreementEdge 384 47 4, 1, 140),
   (.agreementEdge 96 403 2, 1, 35), (.agreementEdge 97 402 2, 1, 70),
   (.agreementEdge 99 400 2, 1, 35), (.agreementEdge 100 402 0, 1, 140),
   (.agreementEdge 402 100 0, 1, 140), (.agreementEdge 101 403 0, 1, 140),
   (.agreementEdge 403 101 0, 1, 140), (.shellLower 44, 1, 47),
   (.shellLower 45, 1, 93), (.shellLower 47, 1, 47),
   (.shellLower 100, 1, 35), (.shellLower 101, 1, 70),
   (.shellLower 103, 1, 35), (.size, 1, 228),
   (.direction 2, 1, 32), (.degree 12, 1, 47),
   (.degree 13, 1, 93), (.degree 15, 1, 47),
   (.degree 32, 1, 4), (.degree 33, 1, 8),
   (.degree 35, 1, 4), (.degree 36, 1, 82),
   (.degree 37, 1, 163), (.degree 39, 1, 82),
   (.half 2, -1, 254), (.half 5, -1, 397),
   (.direction 5, -1, 4), (.degree 28, -1, 26),
   (.degree 29, -1, 53), (.degree 31, -1, 26),
   (.degree 44, -1, 210), (.degree 45, -1, 420),
   (.degree 47, -1, 210), (.degree 100, -1, 140),
   (.degree 103, -1, 140), (.forcedEdge 100 2, 1, 228),
   (.forcedEdge 100 5, 1, 210), (.forcedEdge 101 2, 1, 735),
   (.forcedEdge 101 5, 1, 981), (.forcedEdge 103 2, 1, 228),
   (.forcedEdge 103 5, 1, 210)]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
-- The kernel reduces the 61 sparse rows and combines their orbit coefficients.
/-- The normalized deficit profile `[0,0,4,4,4,5,5,5,5]` is impossible. -/
theorem q9_sixty_six_excludes_004445555 {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i : Fin 9, ((C.filter fun x => x i = true).card : ℤ) +
      2 * (![0, 0, 4, 4, 4, 5, 5, 5, 5] : Fin 9 → ℤ) i = 33) : False := by
  apply certificate_contradiction deficit004445555 certificate004445555
    (by decide +kernel) hC hreg hb hhalf
  · simp only [certificate004445555, List.forall_mem_cons]
    repeat' apply And.intro
    all_goals first | exact List.forall_mem_nil _ | decide +kernel
  · decide +kernel

#print axioms q9_sixty_six_excludes_004445555

end D5.S3.Combinatorics.Graph.HypercubeCritical
