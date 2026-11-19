import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SixtySixAgreementCapacityProbe

/-! A 25-row integer certificate for the normalized Q9 deficit profile 114555555. -/

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

private def deficit (i : Fin 9) : ℤ := if i < 2 then 1 else if i = 2 then 4 else 5

private abbrev Bits := BitVec 9
private abbrev Vertex := Q 9
private abbrev Variable := Bits ⊕ (Bits × Bits)
private abbrev Term := Variable × ℤ

private abbrev cube := cubeBitVec 9
private def bitFlip (x : Bits) (i : Fin 9) : Bits := x ^^^ BitVec.ofNat 9 (2 ^ i.val)
private def weight (x : Bits) : ℤ := ∑ i, if cube x i then deficit i else 0
private def allowed (x : Bits) : Bool := decide (weight x ≤ 16)
private def farAgreement (x y : Bits) (i : Fin 9) : Bool :=
  decide (hammingDist (cube x) (cube y) = 7 ∧ cube x i = cube y i)
private def allowedFar (x y : Bits) : Bool :=
  allowed y && (List.finRange 9).all fun i =>
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
  | agreementEdge (x y : Bits) (i : Fin 9)
  | agreement (x : Bits) (i : Fin 9) (factor : ℤ)

private def Row.terms : Row → List Term
  | .size => cubeTerms allowed (fun x => single x 1)
  | .parity => cubeTerms (fun x => allowed x && cubeParity (cube x)) (fun x => single x 1)
  | .half i => cubeTerms (fun x => allowed x && cube x i) (fun x => single x 1)
  | .direction i => cubeTerms (fun x => allowed x && !(cube x i) && allowed (bitFlip x i))
      (fun x => pair x (bitFlip x i) 1)
  | .degree x => single x (-3) :: termsOf (fun i => allowed (bitFlip x i))
      (fun i => pair x (bitFlip x i) 1)
  | .pairUpper x y => [pair x y 1, single x (-1)]
  | .agreementEdge x y i => [pair x y 1, pair x (bitFlip x i) 1, single x (-1)]
  | .agreement x i factor => single x (-factor) ::
      (if allowed (bitFlip x i) then [pair x (bitFlip x i) factor] else []) ++
      cubeTerms (fun y => farAgreement x y i && allowedFar x y)
        (fun y => pair x y (if factor = 4 then 1 else -1))

private def Row.bound : Row → ℤ
  | .size => 66
  | .parity => 33
  | .half i => 33 - 2 * deficit i
  | .direction _ => 11
  | _ => 0

-- Each entry gives the row, its sign, and its nonnegative multiplier.
private def certificate : List (Row × ℤ × ℤ) :=
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

-- Count the four joint bit patterns in each of the three deficit classes.
private def orderedKey (x y : Bits) : List ℕ :=
  [1, 4, 5].flatMap fun d =>
    let count (a b : Bool) := (univ.filter fun i : Fin 9 =>
      deficit i = d ∧ cube x i = a ∧ cube y i = b).card
    [count false false, count false true, count true false, count true true]

private abbrev Key := Bool × List ℕ

private def orbitKey : Variable → Key
  | .inl x => (false, orderedKey x x)
  | .inr (x, y) =>
    -- Pair membership is symmetric, so either orientation can represent the orbit.
    let a := orderedKey x y
    let b := orderedKey y x
    (true, if a.lex b then a else b)

private def combined : List Term := certificate.flatMap fun (row, sign, w) =>
  row.terms.map fun (v, a) => (v, w * sign * a)

private def upper : ℤ := (certificate.map fun (row, sign, w) => w * sign * row.bound).sum

private def keys (terms : List (Key × ℤ)) : Finset Key := (terms.map Prod.fst).toFinset
private def coefficient (terms : List (Key × ℤ)) (k : Key) : ℤ :=
  (terms.map fun (j, a) => if j = k then a else 0).sum

private def lower (terms : List (Key × ℤ)) : ℤ :=
  ∑ k ∈ keys terms, min 0 (coefficient terms k)

private def keyedTerms : List (Key × ℤ) := combined.map fun (v, a) => (orbitKey v, a)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
-- The kernel reduces the sparse rows and their orbit coefficients.
private theorem certificate_values : lower keyedTerms = -47 ∧ upper = -551 := by
  decide +kernel

noncomputable section

attribute [local instance] Classical.propDecidable

private abbrev Perm := deficitPermutations deficit
private noncomputable instance : Fintype Perm := Fintype.ofFinite Perm

private def value (C : Finset Vertex) : Variable → ℤ
  | .inl x => cubeMembership C (cube x)
  | .inr (x, y) => cubePairMembership C (cube x) (cube y)

private def transportedValue (C : Finset Vertex) (p : Perm) : Variable → ℤ
  | .inl x => cubeMembership C (p • cube x)
  | .inr (x, y) => cubePairMembership C (p • cube x) (p • cube y)

private def average (C : Finset Vertex) (v : Variable) : ℤ :=
  ∑ p : Perm, transportedValue C p v

private lemma orderedKey_orbit {x y u v : Bits} (h : orderedKey x y = orderedKey u v) :
    ∃ p : Perm, p • (cube x, cube y) = (cube u, cube v) := by
  apply joint_bit_counts_same_orbit
  intro d a b
  by_cases hd : d = 1 ∨ d = 4 ∨ d = 5
  · simp only [orderedKey, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.cons.injEq, and_true] at h
    rcases hd with rfl | rfl | rfl <;> cases a <;> cases b <;> tauto
  · have hn (i : Fin 9) : deficit i ≠ d := by
      intro hi
      apply hd
      rw [← hi]
      unfold deficit
      split_ifs <;> simp
    simp [hn]

private lemma average_pair_ordered (C : Finset Vertex) {x y u v : Bits}
    (h : orderedKey x y = orderedKey u v) :
    average C (.inr (x, y)) = average C (.inr (u, v)) := by
  obtain ⟨p, hp⟩ := orderedKey_orbit h
  change (∑ q : Perm, (fun t : Vertex × Vertex => cubePairMembership C t.1 t.2)
    (q • (cube x, cube y))) = ∑ q : Perm, (fun t : Vertex × Vertex => cubePairMembership C t.1 t.2)
      (q • (cube u, cube v))
  rw [← hp]
  exact (orbit_sum_invariant (fun t : Vertex × Vertex => cubePairMembership C t.1 t.2)
    p (cube x, cube y)).symm

private lemma average_swap (C : Finset Vertex) (x y : Bits) :
    average C (.inr (x, y)) = average C (.inr (y, x)) := by
  simp only [average, transportedValue, cubePairMembership, mul_comm]

private lemma average_orbit (C : Finset Vertex) {s t : Variable}
    (h : orbitKey s = orbitKey t) : average C s = average C t := by
  rcases s with x | ⟨x, y⟩ <;> rcases t with u | ⟨u, v⟩
  · have hk : orderedKey x x = orderedKey u u := congrArg Prod.snd h
    obtain ⟨p, hp⟩ := orderedKey_orbit hk
    have he : p • cube x = cube u := congrArg Prod.fst hp
    change (∑ q : Perm, cubeMembership C (q • cube x)) =
      ∑ q : Perm, cubeMembership C (q • cube u)
    rw [← he]
    exact (orbit_sum_invariant (cubeMembership C) p (cube x)).symm
  · cases (congrArg Prod.fst h : false = true)
  · cases (congrArg Prod.fst h : true = false)
  · have hk := congrArg Prod.snd h
    simp only [orbitKey] at hk
    split at hk <;> split at hk
    · exact average_pair_ordered C hk
    · exact (average_pair_ordered C hk).trans (average_swap C v u)
    · exact (average_swap C x y).trans (average_pair_ordered C hk)
    · exact (average_swap C x y).trans
        ((average_pair_ordered C hk).trans (average_swap C v u))

private lemma average_bounds (C : Finset Vertex) (v : Variable) :
    0 ≤ average C v ∧ average C v ≤ Fintype.card Perm := by
  have h (p : Perm) : 0 ≤ transportedValue C p v ∧ transportedValue C p v ≤ 1 := by
    classical
    rcases v with x | ⟨x, y⟩
    · by_cases hx : p • cube x ∈ C <;> simp [transportedValue, cubeMembership, hx]
    · by_cases hx : p • cube x ∈ C <;> by_cases hy : p • cube y ∈ C <;>
        simp [transportedValue, cubePairMembership, cubeMembership, hx, hy]
  refine ⟨sum_nonneg (fun p _ => (h p).1), ?_⟩
  simpa [average] using sum_le_sum (s := (univ : Finset Perm)) (fun p _ => (h p).2)

private def evalTerms (terms : List Term) (z : Variable → ℤ) : ℤ :=
  (terms.map fun (v, a) => a * z v).sum

private lemma eval_transport_sum (C : Finset Vertex) (terms : List Term) :
    evalTerms terms (average C) = ∑ p : Perm, evalTerms terms (transportedValue C p) := by
  induction terms with
  | nil => simp [evalTerms]
  | cons t ts ih =>
    rcases t with ⟨v, a⟩
    simp only [evalTerms, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, average, mul_sum, sum_add_distrib]

private lemma eval_combined (z : Variable → ℤ)
    (h : ∀ t ∈ certificate, t.2.1 * evalTerms t.1.terms z ≤ t.2.1 * t.1.bound)
    (hw : ∀ t ∈ certificate, 0 ≤ t.2.2) :
    evalTerms combined z ≤ upper := by
  unfold combined upper
  suffices ∀ rows : List (Row × ℤ × ℤ), (∀ t ∈ rows, t ∈ certificate) →
      evalTerms (rows.flatMap fun (r, s, w) => r.terms.map fun (v, a) => (v, w * s * a)) z ≤
        (rows.map fun (r, s, w) => w * s * r.bound).sum from this _ (fun _ ht => ht)
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

private lemma lower_bound (C : Finset Vertex) :
    (Fintype.card Perm : ℤ) * lower keyedTerms ≤ evalTerms combined (average C) := by
  classical
  let f (k : Key) := if h : ∃ v, orbitKey v = k then average C (Classical.choose h) else 0
  have hf (v : Variable) : f (orbitKey v) = average C v := by
    have h : ∃ u, orbitKey u = orbitKey v := ⟨v, rfl⟩
    rw [show f (orbitKey v) = average C (Classical.choose h) from dite_eq_left h]
    exact average_orbit C (Classical.choose_spec h)
  have hbox (k : Key) : 0 ≤ f k ∧ f k ≤ Fintype.card Perm := by
    dsimp only [f]
    split
    · exact average_bounds C _
    · simp
  have hgroup := eval_grouped keyedTerms f (keys keyedTerms) (fun k a h => by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(k, a), h, rfl⟩))
  simp only [keyedTerms, List.map_map, Function.comp_def, hf] at hgroup
  rw [show evalTerms combined (average C) = _ from hgroup, lower, mul_sum]
  apply sum_le_sum
  intro k _
  let a := coefficient keyedTerms k
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

private lemma deficit_range (i : Fin 9) : 0 ≤ deficit i ∧ deficit i ≤ 5 := by
  unfold deficit
  split_ifs <;> decide

private lemma deficit_sum : (∑ i, deficit i) = 36 := by decide +kernel

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

private lemma support_rows {C : Finset Vertex} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set Vertex)).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i, ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33) :
    ∀ t ∈ certificate, t.2.1 * evalTerms t.1.terms (value C) ≤ t.2.1 * t.1.bound := by
  classical
  have hd := huang_balanced_cubic_sixty_six_diameter_le_seven hC hreg hb
  have hshell (x : Vertex) (hx : x ∈ C) :
      (shell C x 7).card ≤ 8 ∧
      2 * (∑ i, if x i then deficit i else 0) + 12 ≤ (∑ i, deficit i) + (shell C x 7).card :=
    ⟨sixty_six_distance_seven_le_eight hC hreg hb hd hx,
      coordinate_profile_weight_bound hC hreg hb (fun _ => true) deficit hhalf hx⟩
  have hallow (x : Bits) (hx : cube x ∈ C) : allowed x = true := by
    obtain ⟨hc, hw⟩ := hshell (cube x) hx
    rw [deficit_sum] at hw
    change 2 * weight x + 12 ≤ 36 + ((shell C (cube x) 7).card : ℤ) at hw
    exact decide_eq_true (show weight x ≤ 16 by omega)
  have hz (x : Bits) (hx : ¬ (allowed x = true)) : cubeMembership C (cube x) = 0 := by
    have hn : cube x ∉ C := fun h => hx (hallow x h)
    simp [cubeMembership, hn]
  have hzPair (x y : Bits) (hx : ¬ (allowed x = true ∧ allowed y = true)) :
      cubePairMembership C (cube x) (cube y) = 0 := by
    by_cases hx' : allowed x = true
    · simp [cubePairMembership, hz y (fun hy => hx ⟨hx', hy⟩)]
    · simp [cubePairMembership, hz x hx']
  have hzFar (x y : Bits) (i : Fin 9) (h : farAgreement x y i = true)
      (hn : ¬ allowedFar x y = true) : cubePairMembership C (cube x) (cube y) = 0 := by
    by_cases hx : cube x ∈ C <;> by_cases hy : cube y ∈ C
    · exfalso
      apply hn
      simp only [allowedFar, Bool.and_eq_true, hallow y hy, true_and, List.all_eq_true]
      intro j _
      by_cases hj : cube x j = true
      · by_cases hej : cube y j = cube x j
        · have hm := distance_seven_agreement_excludes_minority hC hreg hb hd (fun _ => true)
            deficit deficit_range hhalf hx hy (of_decide_eq_true h).1 hej.symm hj
          simp [hj, hej, show ¬ 1 < deficit j from not_lt.mpr hm]
        · have hfalse : cube y j = false :=
            Bool.eq_false_of_not_eq_true (fun htrue => hej (htrue.trans hj.symm))
          simp [hfalse]
      · have hj' : cube x j = false := Bool.eq_false_of_not_eq_true hj
        simp [hj']
    all_goals simp [cubePairMembership, cubeMembership, hx, hy]
  obtain ⟨hsize, hparity, hhalf', hdir⟩ := half_eq_rows hC hreg hb hhalf
  have hsingle (p : Vertex → Bool) :
      evalTerms (cubeTerms (fun x => allowed x && p (cube x)) (fun x => single x 1)) (value C) =
      ∑ x ∈ univ.filter (fun x => p x), cubeMembership C x := by
    simp only [eval_cubeTerms, single, value, Equiv.apply_symm_apply, one_mul, Bool.and_eq_true]
    apply sum_filter_weaken
    · exact fun _ h => h.2
    · intro x h hx
      simpa using hz (cube.symm x) (fun ha => hx ⟨ha, h⟩)
  have hs : evalTerms Row.size.terms (value C) = 66 := by
    simpa [Row.terms] using (hsingle (fun _ => true)).trans (by simpa using hsize)
  have hp : evalTerms Row.parity.terms (value C) = 33 := (hsingle cubeParity).trans (hparity true)
  have hh (i : Fin 9) : evalTerms (Row.half i).terms (value C) = (Row.half i).bound :=
    (hsingle (fun x => x i)).trans (hhalf' i)
  have he (i : Fin 9) : evalTerms (Row.direction i).terms (value C) = 11 := by
    rw [Row.terms, eval_cubeTerms, ← hdir i]
    simp only [pair, value, cube_bitFlip, Equiv.apply_symm_apply, one_mul, Bool.and_eq_true,
      Bool.not_eq_true']
    apply sum_filter_weaken
    · exact fun _ h => h.1.2
    · intro x hx hf
      simpa only [cube_bitFlip, Equiv.apply_symm_apply] using
        hzPair (cube.symm x) (bitFlip (cube.symm x) i) (fun h => hf ⟨⟨h.1, hx⟩, h.2⟩)
  have hn (x : Bits) (i : Fin 9) (h : ¬ allowed (bitFlip x i) = true) :
      cubePairMembership C (cube x) (flip (cube x) i) = 0 := by
    simpa only [cube_bitFlip] using hzPair x (bitFlip x i) (fun h' => h h'.2)
  have hc (x : Bits) : evalTerms (Row.degree x).terms (value C) = 0 := by
    simp only [Row.terms, evalTerms, List.map_cons, List.sum_cons, single, value]
    change -3 * cubeMembership C (cube x) +
      evalTerms (termsOf _ _) (value C) = 0
    simp only [eval_termsOf, pair, value, cube_bitFlip, one_mul]
    have h := cube_lifted_incidence_rows hreg hshell (cube x)
    rw [show (∑ i ∈ univ.filter (fun i => allowed (bitFlip x i)), _) =
        ∑ i, cubePairMembership C (cube x) (flip (cube x) i) from by
      rw [← filter_true_of_mem (s := (univ : Finset (Fin 9))) (p := fun _ => True)
        (fun _ _ => trivial)]
      exact sum_filter_weaken _ _ _ (fun _ _ => trivial) (fun i _ hi => hn x i hi)]
    linarith only [h.1]
  have hagree (x : Bits) (i : Fin 9) (k : ℤ) :
      evalTerms (Row.agreement x i k).terms (value C) =
        (if k = 4 then 1 else -1) *
          (∑ y ∈ univ.filter (fun y => hammingDist (cube x) y = 7 ∧ cube x i = y i),
            cubePairMembership C (cube x) y) -
        k * (cubeMembership C (cube x) - cubePairMembership C (cube x) (flip (cube x) i)) := by
    have hfar :
        evalTerms (cubeTerms (fun y => farAgreement x y i && allowedFar x y)
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
            hzFar x (cube.symm y) i hdy (fun ha => hny ⟨hdy, ha⟩), mul_zero]
    have hnear : evalTerms (if allowed (bitFlip x i) then
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
  have hcap (x : Bits) (i : Fin 9) : evalTerms (Row.agreement x i 4).terms (value C) ≤ 0 := by
    have h := (cube_lifted_agreement_capacity hreg hb hd (cube x) i).1
    rw [hagree]
    simpa using sub_nonpos.mpr h
  have hfloor (x : Bits) (i : Fin 9) (hx : weight x = 16) :
      evalTerms (Row.agreement x i (-2)).terms (value C) ≤ 0 := by
    rw [hagree]
    have h := (cube_lifted_agreement_capacity hreg hb hd (cube x) i).2
    by_cases hm : cube x ∈ C
    · obtain ⟨hc', hw⟩ := hshell (cube x) hm
      change 2 * weight x + 12 ≤ (∑ i, deficit i) + ((shell C (cube x) 7).card : ℤ) at hw
      rw [deficit_sum, hx] at hw
      have h8 : (shell C (cube x) 7).card = 8 := by omega
      have hf := h h8
      norm_num
      linarith only [hf]
    · simp [cubePairMembership, cubeMembership, hm]
  have hpair (x y : Bits) :
      evalTerms (Row.pairUpper x y).terms (value C) ≤ 0 := by
    have h := (cube_lifted_pair_rows C (cube x) (cube y)).1
    simp [Row.terms, evalTerms, single, pair, value]
    linarith only [h]
  have hedge (x y : Bits) (i : Fin 9) (h : farAgreement x y i = true) :
      evalTerms (Row.agreementEdge x y i).terms (value C) ≤ 0 := by
    have hf : hammingDist (cube x) (cube y) = 7 ∧ cube x i = cube y i := of_decide_eq_true h
    have he' := cube_lifted_agreement_row hd hf.1 hf.2
    simp [Row.terms, evalTerms, single, pair, value, cube_bitFlip]
    linarith only [he']
  simp only [certificate, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals try exact List.forall_mem_nil _
  all_goals simp only [one_mul, hs, hp, hh, he, hc, Row.bound, mul_zero, le_refl]
  all_goals
    first
    | exact hpair 450 56
    | exact hedge 56 450 0 (by decide +kernel)
    | exact hcap _ _
    | exact hfloor 31 _ (by decide +kernel)
    | exact hfloor 57 _ (by decide +kernel)

/-- No Huang-balanced induced cubic 66-point support has normalized deficit
profile `[1,1,4,5,5,5,5,5,5]` on its true coordinate halves. -/
theorem q9_sixty_six_excludes_114555555 {C : Finset (Q 9)} (hC : C.card = 66)
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hhalf : ∀ i : Fin 9, ((C.filter fun x => x i = true).card : ℤ) +
      2 * (![1, 1, 4, 5, 5, 5, 5, 5, 5] : Fin 9 → ℤ) i = 33) : False := by
  classical
  have hr : ∀ i : Fin 9, deficit i = (![1, 1, 4, 5, 5, 5, 5, 5, 5] : Fin 9 → ℤ) i := by
    decide +kernel
  have hh (i : Fin 9) : ((C.filter fun x => x i = true).card : ℤ) + 2 * deficit i = 33 := by
    rw [hr]
    exact hhalf i
  have hw : ∀ t ∈ certificate, 0 ≤ t.2.2 := by
    simp only [certificate, List.forall_mem_cons]
    repeat' apply And.intro
    all_goals first | exact List.forall_mem_nil _ | decide +kernel
  have hrows (p : Perm) : evalTerms combined (transportedValue C p) ≤ upper := by
    obtain ⟨T, hT, hregT, hbT, hhT, hp⟩ := transport_lifted_cube_support hC hreg hb hh p
    have he : transportedValue C p = value T := by
      funext v
      rcases v with x | ⟨x, y⟩
      · exact (hp (cube x)).symm
      · simp only [transportedValue, value, cubePairMembership, hp]
    rw [he]
    exact eval_combined (value T) (support_rows hT hregT hbT hhT) hw
  have hu : evalTerms combined (average C) ≤ (Fintype.card Perm : ℤ) * upper := by
    rw [eval_transport_sum]
    simpa only [sum_const, card_univ, nsmul_eq_mul] using
      sum_le_sum (s := (univ : Finset Perm)) (fun p _ => hrows p)
  have h := (lower_bound C).trans hu
  rw [certificate_values.1, certificate_values.2] at h
  have hd : 0 < (Fintype.card Perm : ℤ) := by exact_mod_cast Fintype.card_pos
  linarith

#print axioms q9_sixty_six_excludes_114555555

end

end D5.S3.Combinatorics.Graph.HypercubeCritical
