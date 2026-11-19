import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbedding
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9OrbitCertificateProbe
import Batteries.Tactic.OpenPrivate

/-! Exhaustive extension of the five root patterns. A prefix survives if
its vertices are distinct and each placed edge still has an admissible
middle relative to the placed vertices. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch

open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced flip_adj)
open BalancedCubeLowerBound (coordinateSlice)
open Q9SeventyTwoThinSlice (modelRootNeighbors rootSecondAxes)
open Q9EightCubicGraphCertificate (modelAdj)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth

attribute [local instance] Classical.propDecidable
local notation "flip" => BalancedCriticalSpectrum.flip

abbrev Placement := Fin 8 → BitVec 9

private def toggle (x : BitVec 9) (i : Fin 9) : BitVec 9 :=
  x ^^^ BitVec.ofNat 9 (2 ^ i.val)

private def hasTwoSetBits (x : BitVec 9) : Bool :=
  let y := x &&& (x - 1)
  y != 0 && (y &&& (y - 1)) == 0

private theorem hasTwoSetBits_of_two_toggles (i j : Fin 9) (h : i ≠ j) :
    hasTwoSetBits (toggle (toggle 0 i) j) = true := by
  fin_cases i <;> fin_cases j <;> first | contradiction | decide +kernel

private def adjacent (x y : BitVec 9) : Bool :=
  (List.finRange 9).any (fun i => toggle x i == y)

private theorem adjacent_iff (x y : BitVec 9) :
    adjacent x y = true ↔ (hypercube 9).Adj (cubeBitVec 9 x) (cubeBitVec 9 y) := by
  rw [adjacent, List.any_eq_true]
  constructor
  · rintro ⟨i, _, hi⟩
    have hx := beq_iff_eq.mp hi
    rw [← hx, toggle, cubeBitVec_xor_single]
    exact flip_adj _ _
  · intro h
    obtain ⟨i, hi⟩ := adjacent_exists_flip h
    refine ⟨i, List.mem_finRange i, beq_iff_eq.mpr ?_⟩
    apply (cubeBitVec 9).injective
    rw [toggle, cubeBitVec_xor_single, hi]
    rfl

private def permitsMiddle (placed : List (Fin 8)) (p : Placement)
    (i j : Fin 8) : Bool :=
  (List.finRange 9).any fun a =>
    let m := toggle (p i) a
    !m.getLsbD 0 && placed.all fun k => adjacent m (p k) == (k == i || k == j)

private def valid (wagner : Bool) (placed : List (Fin 8)) (p : Placement) : Bool :=
  placed.all fun i => placed.all fun j =>
    if i = j then true else p i != p j &&
      (!modelAdj wagner i j || (hasTwoSetBits (p i ^^^ p j) && permitsMiddle placed p i j))

private def initialLabels (wagner : Bool) : List (Fin 8) :=
  0 :: List.ofFn (modelRootNeighbors wagner)

private def remainingLabels (wagner : Bool) : List (Fin 8) :=
  if wagner then [2, 3, 5, 6] else [3, 5, 6, 7]

private def anchor (wagner : Bool) (i : Fin 8) : Fin 8 :=
  if wagner then (if i = 2 ∨ i = 5 then 1 else 2)
  else if i = 6 then 2 else if i = 7 then 3 else 1

private def startsFromPlaced (wagner : Bool) (placed : List (Fin 8)) :
    List (Fin 8) → Prop
  | [] => True
  | i :: tail => anchor wagner i ∈ placed ∧ modelAdj wagner (anchor wagner i) i = true ∧
      startsFromPlaced wagner (i :: placed) tail

private theorem starting_anchors (wagner : Bool) :
    startsFromPlaced wagner (initialLabels wagner) (remainingLabels wagner) := by
  cases wagner <;>
    simp only [startsFromPlaced, initialLabels, remainingLabels, modelRootNeighbors, anchor,
      Bool.false_eq_true, ite_false, ite_true] <;> decide

private def moves (x : BitVec 9) : List (BitVec 9) :=
  (List.finRange 9).flatMap fun a =>
    ((List.finRange 9).filter (a < ·)).map fun b => toggle (toggle x a) b

private theorem two_toggles_mem_moves (x : BitVec 9) (a b : Fin 9) (h : a ≠ b) :
    toggle (toggle x a) b ∈ moves x := by
  unfold moves
  rcases lt_or_gt_of_ne h with hab | hba
  · exact List.mem_flatMap.mpr ⟨a, List.mem_finRange _, List.mem_map.mpr
      ⟨b, List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true hab⟩, rfl⟩⟩
  · refine List.mem_flatMap.mpr ⟨b, List.mem_finRange _, List.mem_map.mpr
      ⟨a, List.mem_filter.mpr ⟨List.mem_finRange _, decide_eq_true hba⟩, ?_⟩⟩
    simp only [toggle, BitVec.xor_assoc x, BitVec.xor_comm (BitVec.ofNat 9 (2 ^ b.val))]

private def initialPoint (pattern : Fin 5) (a : Fin 3) : BitVec 9 :=
  toggle (toggle 0 ((a.castLE (by decide : 3 ≤ 8)).succ)) (rootSecondAxes pattern a)

private def initialPlacement (wagner : Bool) (pattern : Fin 5) : Placement :=
  fun i => if i = modelRootNeighbors wagner 0 then initialPoint pattern 0
    else if i = modelRootNeighbors wagner 1 then initialPoint pattern 1
    else if i = modelRootNeighbors wagner 2 then initialPoint pattern 2
    else 0

private def fill (wagner : Bool) (placed : List (Fin 8))
    (p : Placement) : List (Fin 8) → List Placement
  | [] => [p]
  | i :: tail => (moves (p (anchor wagner i))).flatMap fun x =>
      let q := Function.update p i x
      if !x.getLsbD 0 && valid wagner (i :: placed) q then
        fill wagner (i :: placed) q tail
      else []

/-- Candidates before removing unused-coordinate relabelings or testing signs. -/
def candidates (wagner : Bool) (pattern : Fin 5) : List Placement :=
  fill wagner (initialLabels wagner) (initialPlacement wagner pattern) (remainingLabels wagner)

private theorem valid_of_actual (wagner : Bool) (placed : List (Fin 8)) (q p : Placement)
    (hagrees : ∀ k ∈ placed, q k = p k)
    (hinj : Function.Injective p)
    (hmid : ∀ i j, modelAdj wagner i j = true →
      ∃ m : BitVec 9, m.getLsbD 0 = false ∧ ∀ k,
        (hypercube 9).Adj (cubeBitVec 9 m) (cubeBitVec 9 (p k)) ↔ k = i ∨ k = j) :
    valid wagner placed q = true := by
  unfold valid
  apply List.all_eq_true.mpr
  intro i hi
  apply List.all_eq_true.mpr
  intro j hj
  by_cases h : i = j
  · simp [h]
  · have hne : (p i == p j) = false := beq_eq_false_iff_ne.mpr (hinj.ne h)
    simp only [h, ite_false, hagrees i hi, hagrees j hj, bne, hne, Bool.not_false, Bool.true_and]
    by_cases hij : modelAdj wagner i j = true
    · simp only [hij, Bool.not_true, Bool.false_or]
      obtain ⟨m, h0, hm⟩ := hmid i j hij
      have hmi := (hm i).mpr (Or.inl rfl)
      obtain ⟨a, ha⟩ := adjacent_exists_flip hmi.symm
      have hm_eq : toggle (p i) a = m := by
        apply (cubeBitVec 9).injective
        rw [toggle, cubeBitVec_xor_single, ha]
        rfl
      obtain ⟨d, hd⟩ := adjacent_exists_flip ((hm j).mpr (Or.inr rfl))
      have hpj : p j = toggle m d := by
        apply (cubeBitVec 9).injective
        rw [toggle, cubeBitVec_xor_single, hd]
        rfl
      have had : a ≠ d := by
        intro had
        subst d
        apply hinj.ne h
        rw [hpj, ← hm_eq]
        simp [toggle, BitVec.xor_assoc]
      have hs : hasTwoSetBits (p i ^^^ p j) = true := by
        have he : p i ^^^ p j = toggle (toggle 0 a) d := by
          rw [hpj, ← hm_eq]
          simp [toggle, ← BitVec.xor_assoc]
        rw [he]
        exact hasTwoSetBits_of_two_toggles a d had
      rw [hs, Bool.true_and]
      unfold permitsMiddle
      apply List.any_eq_true.mpr
      refine ⟨a, List.mem_finRange a, ?_⟩
      simp only [hagrees i hi, hm_eq, h0, Bool.not_false, Bool.true_and]
      apply List.all_eq_true.mpr
      intro k hk
      apply beq_iff_eq.mpr
      rw [hagrees k hk]
      have hiff := (adjacent_iff m (p k)).trans (hm k)
      cases he : adjacent m (p k)
      · have hn : ¬ (k = i ∨ k = j) := fun hk => by simpa [he] using hiff.mpr hk
        simp [not_or.mp hn]
      · rcases hiff.mp he with rfl | rfl <;> simp
    · simp [Bool.eq_false_iff.mpr hij]

private theorem mem_fill (wagner : Bool) (p : Placement)
    (hinj : Function.Injective p) (hcut : ∀ k, (p k).getLsbD 0 = false)
    (hmid : ∀ i j, modelAdj wagner i j = true →
      ∃ m : BitVec 9, m.getLsbD 0 = false ∧ ∀ k,
        (hypercube 9).Adj (cubeBitVec 9 m) (cubeBitVec 9 (p k)) ↔ k = i ∨ k = j)
    (tail placed : List (Fin 8)) (q : Placement)
    (hanchors : startsFromPlaced wagner placed tail)
    (hagrees : ∀ k ∈ placed, q k = p k) :
    ∃ r ∈ fill wagner placed q tail, ∀ k ∈ tail ++ placed, r k = p k := by
  induction tail generalizing placed q with
  | nil => exact ⟨q, by simp [fill], hagrees⟩
  | cons i tail ih =>
    obtain ⟨ha, he, htail⟩ := hanchors
    let q' := Function.update q i (p i)
    have hq' (k : Fin 8) (hk : k ∈ i :: placed) : q' k = p k := by
      rcases List.mem_cons.mp hk with rfl | hk
      · simp [q']
      · by_cases hki : k = i
        · simp [q', hki]
        · simp [q', hki, hagrees k hk]
    obtain ⟨r, hr, hrp⟩ := ih (i :: placed) q' htail hq'
    refine ⟨r, ?_, ?_⟩
    · unfold fill
      apply List.mem_flatMap.mpr
      have hmove : p i ∈ moves (q (anchor wagner i)) := by
        rw [hagrees _ ha]
        obtain ⟨m, _, hm⟩ := hmid _ _ he
        obtain ⟨a, hat⟩ := adjacent_exists_flip ((hm (anchor wagner i)).mpr (Or.inl rfl)).symm
        obtain ⟨b, hbt⟩ := adjacent_exists_flip ((hm i).mpr (Or.inr rfl))
        have hpoint : p i = toggle (toggle (p (anchor wagner i)) a) b := by
          apply (cubeBitVec 9).injective
          simp only [toggle, cubeBitVec_xor_single, hbt, hat]
          rfl
        have hab : a ≠ b := by
          intro hab
          subst b
          have hsame : p i = p (anchor wagner i) := by
            rw [hpoint]
            simp [toggle, BitVec.xor_assoc]
          have hs := hinj hsame
          have hno : ∀ (w : Bool) (v : Fin 8), modelAdj w v v ≠ true := by decide
          exact hno _ _ ((congrArg (modelAdj wagner (anchor wagner i)) hs).symm.trans he)
        rw [hpoint]
        exact two_toggles_mem_moves _ _ _ hab
      refine ⟨p i, hmove, ?_⟩
      have hvalid := valid_of_actual wagner (i :: placed) q' p hq' hinj hmid
      change r ∈ (if !(p i).getLsbD 0 && valid wagner (i :: placed) q' then
          fill wagner (i :: placed) q' tail else [])
      simpa only [hcut, Bool.not_false, Bool.true_and, hvalid, ite_true] using hr
    · intro k hk
      apply hrp k
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hk ⊢
      tauto

/-- Every actual half has an embedding among these candidates. -/
theorem exists_member {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    ∃ (g : Q 9 ≃ Q 9) (σ : Fin 9 ≃ Fin 9)
      (wagner : Bool) (pattern : Fin 5) (p : Fin 8 ↪ Q 9),
      (∀ x i, g (flip x i) = flip (g x) (σ i)) ∧
      (∀ x, g x 0 = false ↔ x 0 = b) ∧
      (∀ k, p k ∈ (coordinateSlice C b).image g) ∧
      (fun i => (cubeBitVec 9).symm (p i)) ∈ candidates wagner pattern ∧
      ∀ i j, modelAdj wagner i j = true →
        ∃ m ∈ (coordinateSlice C b).image g, m 0 = false ∧
          ∀ k, (hypercube 9).Adj m (p k) ↔ k = i ∨ k = j := by
  obtain ⟨g, σ, wagner, pattern, p, hg, hcut, hroot, hhigh, hpoints, hmid⟩ :=
    Q9SeventyTwoEmbedding.normalized_embedding hC hr hb b hs
  let actual : Placement := fun k => (cubeBitVec 9).symm (p k)
  have hplane (k : Fin 8) : (actual k).getLsbD 0 = false := by
    change cubeBitVec 9 (actual k) 0 = false
    simpa [actual] using (hhigh k).2
  have hstep (x : BitVec 9) (a : Fin 9) :
      cubeBitVec 9 (toggle x a) = flip (cubeBitVec 9 x) a := cubeBitVec_xor_single x a
  have hzero : cubeBitVec 9 (0 : BitVec 9) = Q9GrayPlacementNormalForm.origin := by decide
  have hinit (k : Fin 8) (hk : k ∈ initialLabels wagner) :
      initialPlacement wagner pattern k = actual k := by
    rcases List.mem_cons.mp hk with rfl | hleaf
    · have hinit0 : initialPlacement wagner pattern 0 = 0 := by cases wagner <;> rfl
      apply (cubeBitVec 9).injective
      rw [hinit0, hzero]
      simpa [actual] using hroot.symm
    · obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hleaf
      have hi : initialPlacement wagner pattern (modelRootNeighbors wagner a) =
          initialPoint pattern a := by cases wagner <;> fin_cases a <;> rfl
      apply (cubeBitVec 9).injective
      rw [hi, initialPoint, hstep, hstep, hzero]
      simpa [actual] using (hpoints a).symm
  have hmid' (i j : Fin 8) (hij : modelAdj wagner i j = true) :
      ∃ m : BitVec 9, m.getLsbD 0 = false ∧ ∀ k,
        (hypercube 9).Adj (cubeBitVec 9 m) (cubeBitVec 9 (actual k)) ↔ k = i ∨ k = j := by
    obtain ⟨m, _, hm0, hm⟩ := hmid i j hij
    refine ⟨(cubeBitVec 9).symm m, ?_, ?_⟩
    · change cubeBitVec 9 ((cubeBitVec 9).symm m) 0 = false
      simpa using hm0
    · simpa [actual] using hm
  obtain ⟨r, hmem, heq⟩ := mem_fill wagner actual
    ((cubeBitVec 9).symm.injective.comp p.injective) hplane hmid'
    (remainingLabels wagner) (initialLabels wagner) (initialPlacement wagner pattern)
    (starting_anchors wagner) hinit
  have hlabels : ∀ (w : Bool) (k : Fin 8), k ∈ remainingLabels w ++ initialLabels w := by
    decide
  have hrp : r = actual := funext fun k => heq k (hlabels wagner k)
  rw [hrp] at hmem
  exact ⟨g, σ, wagner, pattern, p, hg, hcut, fun k => (hhigh k).1, hmem, hmid⟩

#print axioms exists_member

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbeddingSearch
