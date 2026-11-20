/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedIncidence
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FoldedIncidence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Incidence bounds for coordinate fibres of a parity-folded cubic support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary

/-! Folded degrees count the identity and coordinate translations with multiplicity.
Summing over quotient fibres gives the local cubic projection test. -/

set_option autoImplicit false

open scoped BigOperators

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedIncidence

open BalancedCriticalSpectrum (Q flip flip_flip)

open Classical in
/-- The number of labels whose permutation sends a selected source to the target. -/
noncomputable def incidenceDegree {ι α : Type*} [Fintype ι]
    (e : ι → Equiv.Perm α) (S : Finset α) (x : α) : ℕ :=
  (Finset.univ.filter (fun i => (e i).symm x ∈ S)).card

open Classical in
/-- The portion of a finite set lying over a single quotient point. -/
noncomputable def fibreSlice {α β : Type*} (S : Finset α) (π : α → β) (p : β) : Finset α :=
  S.filter (fun x => π x = p)

open Classical in
/-- Count the members of a finite set satisfying a proposition. -/
noncomputable def countWhere {α : Type*} (S : Finset α) (P : α → Prop) : ℕ :=
  (S.filter P).card

private theorem countWhere_eq_card_filter {α : Type*} (S : Finset α) (P : α → Prop)
    [DecidablePred P] : countWhere S P = (S.filter P).card := by
  unfold countWhere
  congr 1
  ext x
  simp only [Finset.mem_filter]

private theorem countWhere_eq_sum {α : Type*} (S : Finset α) (P : α → Prop)
    [DecidablePred P] : countWhere S P = ∑ x ∈ S, if P x then 1 else 0 :=
  (countWhere_eq_card_filter S P).trans (Finset.card_filter P S)

open Classical in
private theorem fibre_sum_eq {ι α β : Type*} [Fintype ι] [Fintype α]
    (e : ι → Equiv.Perm α) (g : ι → Equiv.Perm β) (π : α → β)
    (hπ : ∀ i x, π (e i x) = g i (π x)) (S : Finset α) (p : β) :
    (∑ x ∈ fibreSlice Finset.univ π p, incidenceDegree e S x) =
      ∑ i, (fibreSlice S π ((g i).symm p)).card := by
  simp only [fibreSlice, incidenceDegree, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_filter]
  let term : α → ℕ := fun x => if π x = p then if (e i).symm x ∈ S then 1 else 0 else 0
  change (∑ x, term x) = ∑ x ∈ S, if π x = (g i).symm p then 1 else 0
  rw [← Equiv.sum_comp (e i) term]
  calc
    _ = ∑ x ∈ S, term (e i x) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ S)
      intro x _ hx
      simp [term, hx]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      have hp : π (e i x) = p ↔ π x = (g i).symm p := by
        rw [hπ]
        exact (g i).eq_symm_apply.symm
      simp [term, hx, hp]

open Classical in
/-- Equivariant permutations transport incidence to the quotient. Degree three on the
selected targets and even exterior degree then bound each quotient fibre's counts. -/
theorem equivariant_fibre_incidence {ι α β : Type*} [Fintype ι] [Fintype α]
    (e : ι → Equiv.Perm α) (g : ι → Equiv.Perm β) (π : α → β)
    (hπ : ∀ i x, π (e i x) = g i (π x)) (S T : Finset α)
    (hthree : ∀ x ∈ T, incidenceDegree e S x = 3)
    (heven : ∀ x ∉ T, Even (incidenceDegree e S x))
    (b : ℕ) (hlabels : Fintype.card ι ≤ 2 * b + 1) (p : β) :
    let F := fibreSlice Finset.univ π p
    let covered := countWhere F (fun x => 0 < incidenceDegree e S x)
    let t := countWhere F (fun x => x ∈ T)
    let I := ∑ i, (fibreSlice S π ((g i).symm p)).card
    (∑ x ∈ F, incidenceDegree e S x) = I ∧
      2 * covered + t ≤ I ∧ 3 * t ≤ I ∧ I % 2 = t % 2 ∧
      t ≤ F.card ∧ I ≤ 3 * t + 2 * b * (F.card - t) := by
  dsimp only
  let F := fibreSlice Finset.univ π p
  let d := incidenceDegree e S
  let selected : α → ℕ := fun x => if x ∈ T then 1 else 0
  let covered : α → ℕ := fun x => if 0 < d x then 1 else 0
  have ht : countWhere F (fun x => x ∈ T) = ∑ x ∈ F, selected x :=
    countWhere_eq_sum F (fun x => x ∈ T)
  have hc : countWhere F (fun x => 0 < d x) = ∑ x ∈ F, covered x :=
    countWhere_eq_sum F (fun x => 0 < d x)
  have hcard : countWhere F (fun x => x ∈ T) ≤ F.card := by
    rw [countWhere_eq_card_filter]
    exact Finset.card_filter_le _ _
  have hcharge (x : α) : 2 * covered x + selected x ≤ d x := by
    by_cases hx : x ∈ T
    · norm_num [covered, selected, hx, show d x = 3 from hthree x hx]
    · obtain ⟨q, hq⟩ := heven x hx
      change d x = q + q at hq
      by_cases hpos : 0 < d x
      · simp [covered, selected, hx, hpos]
        omega
      · simp [covered, selected, hx, hpos]
  have hselected (x : α) : 3 * selected x ≤ d x := by
    by_cases hx : x ∈ T <;> simp [selected, hx, show x ∈ T → d x = 3 from hthree x]
  have hparity (x : α) : d x = 2 * (d x / 2) + selected x := by
    by_cases hx : x ∈ T
    · norm_num [selected, hx, show d x = 3 from hthree x hx]
    · obtain ⟨q, hq⟩ := heven x hx
      change d x = q + q at hq
      simp only [selected, hx, ite_false, Nat.add_zero]
      omega
  have hupper (x : α) : d x ≤ 3 * selected x + 2 * b * (if x ∉ T then 1 else 0) := by
    by_cases hx : x ∈ T
    · simp [selected, hx, show d x = 3 from hthree x hx]
    · have hbound : d x ≤ Fintype.card ι := by
        simpa only [d, incidenceDegree, Finset.card_univ] using
          (Finset.card_filter_le (Finset.univ : Finset ι) (fun i => (e i).symm x ∈ S))
      obtain ⟨q, hq⟩ := heven x hx
      change d x = q + q at hq
      simp only [selected, hx, ite_false, not_false_eq_true, ite_true, Nat.mul_zero, Nat.zero_add,
        Nat.mul_one]
      omega
  have heq := fibre_sum_eq e g π hπ S p
  refine ⟨heq, ?_, ?_, ?_, hcard, ?_⟩
  · rw [← heq, hc, ht, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun x _ => hcharge x)
  · rw [← heq, ht, Finset.mul_sum]
    exact Finset.sum_le_sum (fun x _ => hselected x)
  · rw [← heq, ht, Finset.sum_congr rfl (fun x _ => hparity x), Finset.sum_add_distrib,
      ← Finset.mul_sum]
    change (2 * (∑ x ∈ F, d x / 2) + ∑ x ∈ F, selected x) % 2 =
      (∑ x ∈ F, selected x) % 2
    omega
  · have hsum := Finset.sum_le_sum (s := F) (fun x _ => hupper x)
    have hnot : countWhere F (fun x => x ∉ T) = F.card - countWhere F (fun x => x ∈ T) := by
      simp only [countWhere_eq_card_filter]
      have h := Finset.card_filter_add_card_filter_not (s := F) (fun x => x ∈ T)
      omega
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← ht, ← countWhere_eq_sum F (fun x => x ∉ T), hnot] at hsum
    rw [← heq]
    exact hsum

/-- Restriction to a list of distinct retained coordinate axes. -/
def restrictCoordinates {n k : ℕ} (a : Fin k ↪ Fin n) (x : Q n) : Q k :=
  fun j => x (a j)

private def flipPerm {n : ℕ} (i : Fin n) : Equiv.Perm (Q n) :=
  (show Function.Involutive (fun x => flip x i) from fun x => flip_flip x i).toPerm _

/-- The labels on a folded cube are the identity and one flip per axis. -/
def foldedStep (n : ℕ) : Option (Fin n) → Equiv.Perm (Q n)
  | none => Equiv.refl _
  | some i => flipPerm i

open Classical in
private noncomputable def quotientStep {n k : ℕ} (a : Fin k ↪ Fin n) :
    Option (Fin n) → Equiv.Perm (Q k)
  | none => Equiv.refl _
  | some i => if hi : i ∈ Set.range a then flipPerm (Classical.choose hi) else Equiv.refl _

open Classical in
private theorem quotientStep_retained {n k : ℕ} (a : Fin k ↪ Fin n) (j : Fin k) :
    quotientStep a (some (a j)) = flipPerm j := by
  have hj : a j ∈ Set.range a := ⟨j, rfl⟩
  rw [quotientStep, dite_eq_left hj, a.injective (Classical.choose_spec hj)]

open Classical in
private theorem restrict_step {n k : ℕ} (a : Fin k ↪ Fin n) (i : Option (Fin n)) (x : Q n) :
    restrictCoordinates a (foldedStep n i x) = quotientStep a i (restrictCoordinates a x) := by
  cases i with
  | none => rfl
  | some i =>
    by_cases hi : i ∈ Set.range a
    · obtain ⟨j, rfl⟩ := hi
      rw [quotientStep_retained]
      funext l
      by_cases h : l = j
      · subst l
        simp [foldedStep, flipPerm, restrictCoordinates]
      · have ha : a l ≠ a j := fun he => h (a.injective he)
        simp [foldedStep, flipPerm, restrictCoordinates, BalancedCriticalSpectrum.flip, h, ha]
    · funext l
      have ha : a l ≠ i := fun he => hi ⟨l, he⟩
      simp [quotientStep, hi, foldedStep, flipPerm, restrictCoordinates,
        BalancedCriticalSpectrum.flip, ha]

open Classical in
private theorem coordinate_fibre_card {n k : ℕ} (a : Fin k ↪ Fin n) (p : Q k) :
    (fibreSlice Finset.univ (restrictCoordinates a) p).card = 2 ^ (n - k) := by
  let F := fibreSlice Finset.univ (restrictCoordinates a) p
  let O := {i : Fin n // i ∉ Set.range a}
  have hF (x : Q n) : x ∈ F ↔ restrictCoordinates a x = p := by simp [F, fibreSlice]
  let e : ↥F ≃ (O → Bool) :=
    { toFun := fun x i => x.val i.val
      invFun := fun y =>
        ⟨fun i => if hi : i ∈ Set.range a then p (Classical.choose hi) else y ⟨i, hi⟩,
          (hF _).mpr (by
            funext j
            have hj : a j ∈ Set.range a := ⟨j, rfl⟩
            change (if hi : a j ∈ Set.range a then p (Classical.choose hi)
              else y ⟨a j, hi⟩) = p j
            rw [dite_eq_left hj, a.injective (Classical.choose_spec hj)])⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext i
        dsimp only
        split
        · rename_i hi
          rw [← congrFun ((hF _).mp x.property) (Classical.choose hi)]
          exact congrArg x.val (Classical.choose_spec hi)
        · rfl
      right_inv := by
        intro y
        funext i
        exact dite_eq_right i.property }
  change F.card = _
  rw [← Fintype.card_coe F, Fintype.card_congr e, Fintype.card_fun, Fintype.card_bool]
  change 2 ^ Fintype.card {i : Fin n // i ∉ Set.range a} = _
  rw [Fintype.card_subtype_compl, Fintype.card_range a, Fintype.card_fin, Fintype.card_fin]

open Classical in
private theorem coordinate_incidence_sum {n k : ℕ} (a : Fin k ↪ Fin n) (f : Q k → ℕ) (p : Q k) :
    (∑ i, f ((quotientStep a i).symm p)) = (n + 1 - k) * f p + ∑ j, f (flip p j) := by
  let A := (Finset.univ : Finset (Fin k)).map a
  let weight (i : Fin n) := f ((quotientStep a (some i)).symm p)
  rw [Fintype.sum_option]
  change f p + ∑ i, weight i = _
  rw [← Finset.sum_add_sum_compl A weight]
  have hkeep : ∑ i ∈ A, weight i = ∑ j, f (flip p j) := by
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro j _
    change f ((quotientStep a (some (a j))).symm p) = f (flip p j)
    rw [quotientStep_retained]
    rfl
  have hdrop : ∑ i ∈ Aᶜ, weight i = (n - k) * f p := by
    calc
      _ = ∑ _i ∈ Aᶜ, f p := by
        apply Finset.sum_congr rfl
        intro i hi
        have hnot : i ∉ Set.range a := by simpa [A] using hi
        change f ((quotientStep a (some i)).symm p) = f p
        rw [quotientStep, dite_eq_right hnot]
        rfl
      _ = _ := by simp [A, Finset.card_compl, smul_eq_mul]
  have hk : k ≤ n := by simpa using Fintype.card_le_of_injective _ a.injective
  rw [hkeep, hdrop, show n + 1 - k = (n - k) + 1 by omega, Nat.add_mul, Nat.one_mul]
  ac_rfl

open Classical in
/-- The local cubic projection test for the two folded parity classes of a nine-cube.
A certified lower bound `L` on the covered count can be used in the interval test. -/
theorem folded_coordinate_incidence {k : ℕ} (a : Fin k ↪ Fin 8) (S T : Finset (Q 8))
    (hthree : ∀ x ∈ T, incidenceDegree (foldedStep 8) S x = 3)
    (heven : ∀ x ∉ T, Even (incidenceDegree (foldedStep 8) S x))
    (p : Q k) :
    let F := fibreSlice Finset.univ (restrictCoordinates a) p
    let d := incidenceDegree (foldedStep 8) S
    let covered := countWhere F (fun x => 0 < d x)
    let t := countWhere F (fun x => x ∈ T)
    let f := fun q => (fibreSlice S (restrictCoordinates a) q).card
    let I := (9 - k) * f p + ∑ j, f (flip p j)
    let M := 2 ^ (8 - k)
    (∑ x ∈ F, d x) = I ∧ 2 * covered + t ≤ I ∧ 3 * t ≤ I ∧ I % 2 = t % 2 ∧
      F.card = M ∧ t ≤ M ∧ I ≤ 3 * t + 8 * (M - t) ∧
      ∀ L ≤ covered,
        let U := min M (min (I / 3) (I - 2 * L))
        max (I % 2) ((I - 8 * M + 4) / 5) ≤ t ∧ t ≤ U - (U + I) % 2 := by
  dsimp only
  have h := equivariant_fibre_incidence (foldedStep 8) (quotientStep a)
    (restrictCoordinates a) (restrict_step a) S T hthree heven 4 (by simp) p
  dsimp only at h
  rw [coordinate_incidence_sum a (fun q => (fibreSlice S (restrictCoordinates a) q).card)
    p, coordinate_fibre_card] at h
  simp only [show (8 : ℕ) + 1 = 9 by decide, show (2 : ℕ) * 4 = 8 by decide] at h
  obtain ⟨hI, hcharge, hthreeT, hmod, ht, hupper⟩ := h
  refine ⟨hI, hcharge, hthreeT, hmod, coordinate_fibre_card a p, ht, hupper, ?_⟩
  intro L hL
  constructor
  · exact max_le (by omega) (by omega)
  · let I := (9 - k) * (fibreSlice S (restrictCoordinates a) p).card +
        ∑ j, (fibreSlice S (restrictCoordinates a) (flip p j)).card
    let t := countWhere (fibreSlice Finset.univ (restrictCoordinates a) p) (fun x => x ∈ T)
    let U := min (2 ^ (8 - k)) (min (I / 3) (I - 2 * L))
    change t ≤ U - (U + I) % 2
    have hU : t ≤ U := le_min ht (le_min (by omega) (by omega))
    change I % 2 = t % 2 at hmod
    clear_value U
    omega

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (IsBalanced flip_adj)
open BalancedCubeComponentBoundary (directions regular_directions exterior_even)
open private cubeParity cubeParity_ne_of_adj from D5.S3.Combinatorics.Graph.HypercubeSubQuorum

open Classical in
/-- Restrict to the given parity and delete the chosen axis in the original nine-cube. -/
noncomputable def foldedParitySet (drop : Fin 9) (p : Bool) (C : Finset (Q 9)) :
    Finset (Q 8) :=
  (C.filter (fun x => cubeParity x = p)).image (restrictCoordinates drop.succAboveEmb)

private theorem parity_flip (x : Q 9) (i : Fin 9) : cubeParity (flip x i) = !cubeParity x := by
  have h := cubeParity_ne_of_adj (flip_adj x i)
  cases hx : cubeParity x <;> cases hy : cubeParity (flip x i) <;> simp_all

open Classical in
private theorem same_of_same_fold (drop : Fin 9) {x y : Q 9}
    (hp : cubeParity x = cubeParity y)
    (he : restrictCoordinates drop.succAboveEmb x = restrictCoordinates drop.succAboveEmb y) :
    x = y := by
  have hkeep (i : Fin 9) (hi : i ≠ drop) : x i = y i := by
    obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
    exact congrFun he j
  by_cases hd : x drop = y drop
  · funext i
    by_cases hi : i = drop
    · exact hi ▸ hd
    · exact hkeep i hi
  · have hy : y = flip x drop := by
      funext i
      by_cases hi : i = drop
      · subst i
        cases hx : x drop <;> cases hy : y drop <;> simp_all
      · simpa [BalancedCriticalSpectrum.flip, hi] using (hkeep i hi).symm
    exact (cubeParity_ne_of_adj (hy.symm ▸ flip_adj x drop) hp).elim

open Classical in
private theorem exists_parity_lift (drop : Fin 9) (p : Bool) (v : Q 8) :
    ∃ x : Q 9, cubeParity x = p ∧ restrictCoordinates drop.succAboveEmb x = v := by
  let x : Q 9 := drop.insertNth false v
  have hx : restrictCoordinates drop.succAboveEmb x = v := by
    funext j
    exact Fin.insertNth_apply_succAbove (α := fun _ => Bool) drop false v j
  by_cases hp : cubeParity x = p
  · exact ⟨x, hp, hx⟩
  · refine ⟨flip x drop, ?_, ?_⟩
    · rw [parity_flip]
      cases h : cubeParity x <;> cases p <;> simp_all
    · rw [← hx]
      funext j
      simp [restrictCoordinates, BalancedCriticalSpectrum.flip, Fin.succAbove_ne]

open Classical in
private theorem mem_foldedParitySet (drop : Fin 9) (p : Bool) (C : Finset (Q 9)) (x : Q 9)
    (hp : cubeParity x = p) :
    restrictCoordinates drop.succAboveEmb x ∈ foldedParitySet drop p C ↔ x ∈ C := by
  constructor
  · intro hm
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    obtain ⟨hyC, hyp⟩ := Finset.mem_filter.mp hy
    exact same_of_same_fold drop (hyp.trans hp.symm) he ▸ hyC
  · intro hx
    exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hp⟩, rfl⟩

open Classical in
private theorem folded_degree_eq_directions (drop : Fin 9) (p : Bool) (C : Finset (Q 9))
    (x : Q 9) (hx : cubeParity x = !p) :
    incidenceDegree (foldedStep 8) (foldedParitySet drop p C)
      (restrictCoordinates drop.succAboveEmb x) = (directions C x).card := by
  unfold incidenceDegree directions
  apply Finset.card_equiv (finSuccEquiv' drop).symm
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  let i := (finSuccEquiv' drop).symm j
  change _ ↔ flip x i ∈ C
  have hpar : cubeParity (flip x i) = p := by simp [parity_flip, hx]
  rw [← mem_foldedParitySet drop p C _ hpar]
  have hstep : (foldedStep 8 j).symm (restrictCoordinates drop.succAboveEmb x) =
      restrictCoordinates drop.succAboveEmb (flip x i) := by
    cases j with
    | none =>
      funext l
      simp [i, foldedStep, restrictCoordinates, BalancedCriticalSpectrum.flip, Fin.succAbove_ne]
    | some j =>
      funext l
      by_cases hl : l = j
      · subst l
        simp [i, foldedStep, flipPerm, restrictCoordinates]
      · have hne : drop.succAbove l ≠ drop.succAbove j :=
          fun he => hl (Fin.succAbove_right_injective he)
        simp [i, foldedStep, flipPerm, restrictCoordinates, BalancedCriticalSpectrum.flip, hl, hne]
  rw [hstep]

open Classical in
/-- Cubicity and Huang balance give degree three on the opposite folded parity
and even degree at every other folded target. -/
theorem folded_degree_of_balanced_cubic (drop : Fin 9) (p : Bool) (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) (hb : IsBalanced C) :
    let S := foldedParitySet drop p C
    let T := foldedParitySet drop (!p) C
    (∀ x ∈ T, incidenceDegree (foldedStep 8) S x = 3) ∧
      (∀ x ∉ T, Even (incidenceDegree (foldedStep 8) S x)) := by
  constructor
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := exists_parity_lift drop (!p) v
    rw [folded_degree_eq_directions drop p C x hx]
    exact regular_directions C hr ((mem_foldedParitySet drop (!p) C x hx).mp hv)
  · intro v hv
    obtain ⟨x, hx, rfl⟩ := exists_parity_lift drop (!p) v
    rw [folded_degree_eq_directions drop p C x hx]
    exact exterior_even C hr hb x (fun he => hv ((mem_foldedParitySet drop (!p) C x hx).mpr he))

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedIncidence
