/- GID: D5/S3/ObserverMemory/Algorithms/FixedForestTargetInventory
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/FixedForestTargetInventory
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Physical complete histories determine literal stationary realizations. -/

import D5.S3.ObserverMemory.Algorithms.StationaryUnitControl
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.FixedForestTargetInventory

open StationaryUnitControl
attribute [local instance] Classical.propDecidable

variable {P h ell e : Nat} {Node : Type} [Fintype Node] [DecidableEq Node]

abbrev Label (P : Nat) := ZMod (3 * P)

/-- Complete histories retain their own read indices. A history has one parent;
its read-control image need not have an acyclic graph. -/
structure PhysicalForest (P h ell : Nat) (Node : Type) [Fintype Node] [DecidableEq Node]
    (hP : 1 < P) where
  parent : Node → Option Node
  root : Fin 3 → Node
  color : Node → Fin 3
  shift : Node → Nat
  level : Node → Nat
  delay : Node → Nat
  leafLabel : Node → Label P
  support : Node → Finset (Label P)
  lower : Node → Nat
  upper : Node → Nat
  reads : Label P → Nat
  event : Label P → Nat → Node
  reads_pos : ∀ x, 0 < reads x
  reads_bound : ∀ x, reads x ≤ h
  root_parent : ∀ c, parent (root c) = none
  root_color : ∀ c, color (root c) = c
  root_shift : ∀ c, shift (root c) = ell
  root_level : ∀ c, level (root c) = 0
  roots_exact : ∀ n, parent n = none ↔ ∃ c, n = root c
  first : ∀ x, event x 0 = root (digit hP (x + (ell : Label P)))
  event_level : ∀ x i, i < reads x → level (event x i) = i
  event_support : ∀ x i, i < reads x → x ∈ support (event x i)
  support_events : ∀ n x, x ∈ support n → ∃ i, i < reads x ∧ event x i = n
  support_nonempty : ∀ n, (support n).Nonempty
  interval : ∀ n x, x ∈ support n ↔
    (color n).val * P + lower n ≤ (x + (shift n : Label P)).val ∧
    (x + (shift n : Label P)).val < (color n).val * P + upper n
  interval_bounds : ∀ n, lower n < upper n ∧ upper n ≤ P
  child_shift : ∀ n p, parent n = some p → shift n = shift p + delay p
  child_level : ∀ n p, parent n = some p → level n = level p + 1
  child_digit_injective : ∀ p n m, parent n = some p → parent m = some p →
    color n = color m → n = m
  successor : ∀ x i, i + 1 < reads x → parent (event x (i + 1)) = some (event x i)
  last : ∀ x n, parent n ≠ some (event x (reads x - 1))
  leaf_original : ∀ n x, x ∈ support n → (∀ m, parent m ≠ some n) → leafLabel n = x
  positive : ∀ n, (∃ m, parent m = some n) → 0 < delay n
  branching : ∀ n, ((Finset.univ.filter (fun m => parent m = some n)).card ≤ 2)
  binary_count : (Finset.univ.filter (fun n =>
    (Finset.univ.filter (fun m => parent m = some n)).card = 2)).card = 3 * (P - 1)

variable {hP : 1 < P} (F : PhysicalForest P h ell Node hP)

namespace PhysicalForest

def children (n : Node) : Finset Node := Finset.univ.filter (fun m => F.parent m = some n)
def Binary (n : Node) : Prop := (F.children n).card = 2
def Unary (n : Node) : Prop := (F.children n).card = 1
def Internal (n : Node) : Prop := (F.children n).Nonempty

def phaseSupport (n : Node) : Finset (Label P) :=
  (F.support n).image (fun x => x + (F.shift n : Label P))

end PhysicalForest

/-- Raw marked source nodes. These are the physical requirements before the
prescribed target/row identifications are checked for compatibility. -/
structure Prescribed (F : PhysicalForest P h ell Node hP) where
  A : Node
  B : Node
  H : Node
  K : Node
  H1 : Node
  K1 : Node
  A_binary : F.Binary A
  B_binary : F.Binary B
  H_binary : F.Binary H
  K_unary : F.Unary K
  H1_unary : F.Unary H1
  K1_unary : F.Unary K1
  AB_distinct : A ≠ B
  marked_distinct : List.Pairwise (· ≠ ·) [H, K, H1, K1]
  HK_parents : (F.parent H = some A ∧ F.parent K = some B) ∨
    (F.parent H = some B ∧ F.parent K = some A)
  HK_color : F.color H = F.color K
  HK_disjoint : Disjoint (F.phaseSupport H) (F.phaseSupport K)
  first_children : F.parent H1 = some H ∧ F.parent K1 = some K
  child_color : F.color H1 = F.color K1
  child_disjoint : Disjoint (F.phaseSupport H1) (F.phaseSupport K1)
  production_wait : F.delay K = F.delay H
  resolving_wait : F.delay K1 = F.delay H1
  resolving_colors : ∀ n m, F.parent n = some H1 → F.parent m = some K1 →
    F.color n ≠ F.color m
  shared_three : ((F.children A ∪ F.children B).image F.color).card = 3

variable (R : Prescribed F)

/-- A represents the A/B merge; Z and all extras are distinct tagged targets. -/
abbrev BinaryTarget := {n : Node // F.Binary n ∧ n ≠ R.B}
abbrev Target := BinaryTarget F R ⊕ (Unit ⊕ Fin e)
abbrev ReadTarget := Unit ⊕ Target (e := e) F R
abbrev Row := ReadTarget (e := e) F R × Fin 3

noncomputable def binaryTarget (n : Node) (hn : F.Binary n) : Target (e := e) F R :=
  .inl (if hb : n = R.B then ⟨R.A, R.A_binary, R.AB_distinct⟩ else ⟨n, hn, hb⟩)

def resolvingTarget : Target (e := e) F R := .inr (.inl ())
def extraTarget (i : Fin e) : Target (e := e) F R := .inr (.inr i)

def Demand (n : Node) : Prop := F.Unary n ∧ n ≠ R.K ∧ n ≠ R.H1 ∧ n ≠ R.K1
abbrev Ordinary := {n : Node // Demand F R n}

/-- Forced rows use only the source parent, its role, and the original digit. -/
noncomputable def forcedRow (n : Node) : Option (Row (e := e) F R) :=
  match F.parent n with
  | none => some (.inl (), F.color n)
  | some p =>
    if hb : F.Binary p then some (.inr (binaryTarget F R p hb), F.color n)
    else if p = R.K then some (.inr (binaryTarget F R R.H R.H_binary), F.color n)
    else if p = R.H1 ∨ p = R.K1 then some (.inr (resolvingTarget F R), F.color n)
    else none

def Shared (n m : Node) : Prop :=
  n = m ∨ (n = R.H ∧ m = R.K) ∨ (n = R.K ∧ m = R.H) ∨
    (n = R.H1 ∧ m = R.K1) ∨ (n = R.K1 ∧ m = R.H1)

/-- A finite structural check. It mentions no controller, assignment,
execution, injection, capacity or realization witness. -/
def Compatible : Prop :=
  ∀ n m row, forcedRow (e := e) F R n = some row →
    forcedRow (e := e) F R m = some row → Shared F R n m

/-- Spare slots are the original absolute digits absent from forced placement. -/
abbrev SpareSlot := {s : Target (e := e) F R × Fin 3 //
  ∀ n, forcedRow F R n ≠ some (.inr s.1, s.2)}

/-- A unary demand's child is selected from the original finite forest. -/
noncomputable def demandChild (d : Ordinary F R) : Node :=
  Classical.choose (Finset.card_pos.mp (show 0 < (F.children d.val).card by
    rw [d.property.1]; omega))

/-- Every extra target is used; no per-color splitting of a target is allowed. -/
structure Assignment where
  slot : Ordinary F R → SpareSlot (e := e) F R
  injective : Function.Injective slot
  same_digit : ∀ d, (slot d).val.2 = F.color (demandChild F R d)
  hits_extra : ∀ i : Fin e, ∃ d, (slot d).val.1 = extraTarget F R i


/-- The original assignment class is finite because only its finite slot map
varies; its remaining fields assert properties of that same map. -/
noncomputable instance assignmentFintype : Fintype (Assignment (e := e) F R) := by
  classical
  letI : Fintype (Ordinary F R) := inferInstance
  letI : Fintype (SpareSlot (e := e) F R) := inferInstance
  letI : Fintype (Ordinary F R → SpareSlot (e := e) F R) := inferInstance
  exact Fintype.ofInjective (fun α : Assignment (e := e) F R => α.slot) (by
    intro α β he
    cases α
    cases β
    cases he
    rfl)

theorem demand_child_parent (d : Ordinary F R) : F.parent (demandChild F R d) = some d.val := by
  have hc := Classical.choose_spec (Finset.card_pos.mp (show 0 < (F.children d.val).card by
    rw [d.property.1]; omega))
  exact (Finset.mem_filter.mp hc).2

noncomputable def baseline (q : Target (e := e) F R) : Nat :=
  match q with
  | .inl b => Finset.univ.sup (fun p => if hp : F.Binary p then
      if binaryTarget (e := e) F R p hp = .inl b then F.delay p else 0 else 0)
  | .inr (.inl _) => F.delay R.H1
  | .inr (.inr _) => 1

noncomputable def L (α : Assignment (e := e) F R) (q : Target (e := e) F R) : Nat :=
  max (baseline F R q) (Finset.univ.sup (fun d : Ordinary F R =>
    if (α.slot d).val.1 = q then F.delay d.val else 0))

/-- The actual target request of each source history. The default at a leaf
is never executed; it merely makes the structural function total. -/
noncomputable def nextTarget (α : Assignment (e := e) F R) (n : Node) : Target (e := e) F R :=
  if hb : F.Binary n then binaryTarget F R n hb
  else if n = R.K then binaryTarget F R R.H R.H_binary
  else if n = R.H1 ∨ n = R.K1 then resolvingTarget F R
  else if hd : Demand F R n then (α.slot ⟨n, hd⟩).val.1
  else resolvingTarget F R

noncomputable def placement (α : Assignment (e := e) F R) (n : Node) : Row (e := e) F R :=
  match F.parent n with
  | none => (.inl (), F.color n)
  | some p => (.inr (nextTarget F R α p), F.color n)

theorem child_internal {n p : Node} (hp : F.parent n = some p) : F.Internal p :=
  ⟨n, by simp [PhysicalForest.children, hp]⟩

theorem internal_positive {n : Node} (hn : F.Internal n) : 0 < F.delay n := by
  obtain ⟨m, hm⟩ := hn
  exact F.positive n ⟨m, (Finset.mem_filter.mp hm).2⟩

theorem internal_binary_or_unary {n : Node} (hn : F.Internal n) :
    F.Binary n ∨ F.Unary n := by
  have hp := Finset.card_pos.mpr hn
  have hb := F.branching n
  change (F.children n).card ≤ 2 at hb
  change (F.children n).card = 2 ∨ (F.children n).card = 1
  omega

theorem unary_child_unique {p n m : Node} (hp : F.Unary p)
    (hn : F.parent n = some p) (hm : F.parent m = some p) : n = m := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hp
  have hna : n ∈ F.children p := by simp [PhysicalForest.children, hn]
  have hma : m ∈ F.children p := by simp [PhysicalForest.children, hm]
  rw [ha] at hna hma
  exact (Finset.mem_singleton.mp hna).trans (Finset.mem_singleton.mp hma).symm

theorem binary_not_unary {n : Node} (hb : F.Binary n) (hu : F.Unary n) : False := by
  change (F.children n).card = 2 at hb
  change (F.children n).card = 1 at hu
  omega

theorem placement_classification (α : Assignment (e := e) F R) (n : Node) :
    forcedRow F R n = some (placement F R α n) ∨
    ∃ d : Ordinary F R, F.parent n = some d.val ∧
      placement F R α n = (.inr (α.slot d).val.1, (α.slot d).val.2) := by
  cases hp : F.parent n with
  | none => exact Or.inl (by simp [forcedRow, placement, hp])
  | some p =>
    by_cases hb : F.Binary p
    · exact Or.inl (by simp [forcedRow, placement, nextTarget, hp, hb])
    by_cases hk : p = R.K
    · have nb : ¬ F.Binary R.K := hk ▸ hb
      exact Or.inl (by simp [forcedRow, placement, nextTarget, hp, hk, nb])
    by_cases hr : p = R.H1 ∨ p = R.K1
    · exact Or.inl (by simp [forcedRow, placement, nextTarget, hp, hb, hk, hr])
    have hu : F.Unary p := (internal_binary_or_unary F (child_internal F hp)).resolve_left hb
    have hd : Demand F R p := ⟨hu, hk, fun hh => hr (Or.inl hh), fun hh => hr (Or.inr hh)⟩
    let d : Ordinary F R := ⟨p, hd⟩
    have he : n = demandChild F R d :=
      unary_child_unique F hu hp (demand_child_parent F R d)
    refine Or.inr ⟨d, rfl, ?_⟩
    simp only [placement, hp, nextTarget, dif_neg hb, if_neg hk, if_neg hr, dif_pos hd]
    congr 1
    exact he ▸ (α.same_digit d).symm

/-- An arbitrary same-digit assignment introduces no third shared history. -/
theorem placement_fibers (hc : Compatible (e := e) F R)
    (α : Assignment (e := e) F R) {n m : Node}
    (he : placement F R α n = placement F R α m) : Shared F R n m := by
  rcases placement_classification F R α n with hn | ⟨d, hd, hn⟩ <;>
    rcases placement_classification F R α m with hm | ⟨f, hf, hm⟩
  · exact hc n m _ hn (he ▸ hm)
  · have hh := (α.slot f).property n
    rw [← hm, ← he] at hh
    exact False.elim (hh hn)
  · have hh := (α.slot d).property m
    rw [← hn, he] at hh
    exact False.elim (hh hm)
  · have hs : (α.slot d).val = (α.slot f).val := by
      have hh := hn.symm.trans (he.trans hm)
      exact Prod.ext (Sum.inr.inj (congrArg Prod.fst hh))
        (congrArg (fun r : Row (e := e) F R => r.2) hh)
    have df : d = f := α.injective (Subtype.ext hs)
    subst f
    exact Or.inl (unary_child_unique F d.property.1 hd hf)

theorem binary_baseline (p : Node) (hp : F.Binary p) :
    F.delay p ≤ baseline (e := e) F R (binaryTarget F R p hp) := by
  unfold binaryTarget
  split_ifs with hb
  all_goals
    simp only [baseline]
    apply Finset.le_sup_of_le (Finset.mem_univ p)
    simp [hp, binaryTarget, hb, R.B_binary]

private theorem ordinary_bound (α : Assignment (e := e) F R) (d : Ordinary F R) :
    F.delay d.val ≤ L F R α (α.slot d).val.1 := by
  apply le_trans _ (le_max_right _ _)
  exact Finset.le_sup_of_le (Finset.mem_univ d) (by simp)

theorem request_bound (α : Assignment (e := e) F R) {n : Node}
    (hn : F.Internal n) : F.delay n ≤ L F R α (nextTarget F R α n) := by
  unfold nextTarget
  split_ifs with hb hk hr hd
  · exact le_trans (binary_baseline F R n hb) (le_max_left _ _)
  · subst n
    rw [R.production_wait]
    exact le_trans (binary_baseline F R R.H R.H_binary) (le_max_left _ _)
  · rcases hr with rfl | rfl
    · exact le_max_left _ _
    · rw [R.resolving_wait]; exact le_max_left _ _
  · exact ordinary_bound F R α ⟨n, hd⟩
  · have hu := (internal_binary_or_unary F hn).resolve_left hb
    exact False.elim (hd ⟨hu, hk, fun hh => hr (Or.inl hh), fun hh => hr (Or.inr hh)⟩)

/-- Digits occupied by the prescribed physical arrivals, before alpha is chosen. -/
noncomputable def occupied (q : Target (e := e) F R) : Finset (Fin 3) :=
  Finset.univ.filter (fun c => ∃ n, forcedRow F R n = some (.inr q, c))

theorem binary_representative (p : Node) (hp : F.Binary p)
    (b : BinaryTarget F R) : binaryTarget (e := e) F R p hp = .inl b ↔
      p = b.val ∨ (b.val = R.A ∧ p = R.B) := by
  unfold binaryTarget
  by_cases hb : p = R.B
  · simp only [dif_pos hb, Sum.inl.injEq, Subtype.ext_iff]
    constructor
    · intro he; exact Or.inr ⟨he.symm, hb⟩
    · rintro (he | ⟨he, _⟩)
      · exact False.elim (b.property.2 (he ▸ hb))
      · exact he.symm
  · simp only [dif_neg hb, Sum.inl.injEq, Subtype.ext_iff]
    constructor
    · exact Or.inl
    · rintro (he | ⟨_, he⟩)
      · exact he
      · exact False.elim (hb he)

private theorem occupied_binary (b : BinaryTarget F R) (c : Fin 3) :
    c ∈ occupied (e := e) F R (.inl b) ↔
    ∃ p, ∃ hp : F.Binary p, binaryTarget (e := e) F R p hp = .inl b ∧
      ∃ n, F.parent n = some p ∧ F.color n = c := by
  simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, he⟩
    cases hp : F.parent n with
    | none => simp [forcedRow, hp] at he
    | some p =>
      by_cases hb : F.Binary p
      · have pair : binaryTarget (e := e) F R p hb = .inl b ∧ F.color n = c := by
          simpa [forcedRow, hp, hb] using he
        exact ⟨p, hb, pair.1, n, hp, pair.2⟩
      by_cases hk : p = R.K
      · have nb : ¬ F.Binary R.K := hk ▸ hb
        have pair : binaryTarget (e := e) F R R.H R.H_binary = .inl b ∧
            F.color n = c := by simpa [forcedRow, hp, hk, nb] using he
        have child : n = R.K1 := unary_child_unique F R.K_unary (hk ▸ hp)
          R.first_children.2
        exact ⟨R.H, R.H_binary, pair.1, R.H1, R.first_children.1,
          R.child_color.trans (child ▸ pair.2)⟩
      by_cases hr : p = R.H1 ∨ p = R.K1
      · simp [forcedRow, hp, hb, hk, hr, resolvingTarget] at he
      · simp [forcedRow, hp, hb, hk, hr] at he
  · rintro ⟨p, hp, ht, n, hn, hc⟩
    exact ⟨n, by simp [forcedRow, hn, hp, ht, hc]⟩

private theorem occupied_binary_image (b : BinaryTarget F R) :
    occupied (e := e) F R (.inl b) =
      (F.children b.val ∪ if b.val = R.A then F.children R.B else ∅).image F.color := by
  ext c
  rw [occupied_binary F R b c]
  constructor
  · rintro ⟨p, hp, ht, n, hn, hc⟩
    rcases (binary_representative F R p hp b).mp ht with he | ⟨he, hpB⟩
    · subst p
      exact Finset.mem_image.mpr ⟨n, Finset.mem_union_left _
        (by simp [PhysicalForest.children, hn]), hc⟩
    · subst p
      exact Finset.mem_image.mpr ⟨n, Finset.mem_union_right _
        (by simp [he, PhysicalForest.children, hn]), hc⟩
  · rintro hc
    obtain ⟨n, hn, hc⟩ := Finset.mem_image.mp hc
    rcases Finset.mem_union.mp hn with hn | hn
    · exact ⟨b.val, b.property.1, (binary_representative F R _ _ b).mpr (Or.inl rfl),
        n, (Finset.mem_filter.mp hn).2, hc⟩
    · by_cases he : b.val = R.A
      · simp only [if_pos he] at hn
        exact ⟨R.B, R.B_binary, (binary_representative F R _ _ b).mpr (Or.inr ⟨he, rfl⟩),
          n, (Finset.mem_filter.mp hn).2, hc⟩
      · simp [he] at hn

private theorem occupied_resolving : occupied (e := e) F R (resolvingTarget F R) =
    (F.children R.H1 ∪ F.children R.K1).image F.color := by
  ext c
  simp only [occupied, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨n, he⟩
    cases hp : F.parent n with
    | none => simp [forcedRow, hp] at he
    | some p =>
      by_cases hb : F.Binary p
      · unfold forcedRow at he
        simp only [hp, dif_pos hb, binaryTarget] at he
        split_ifs at he <;> cases he
      by_cases hk : p = R.K
      · unfold forcedRow at he
        simp only [hp, dif_neg hb, if_pos hk, binaryTarget] at he
        split_ifs at he <;> cases he
      by_cases hr : p = R.H1 ∨ p = R.K1
      · have hc : F.color n = c := by simpa [forcedRow, hp, hb, hk, hr] using he
        apply Finset.mem_image.mpr
        refine ⟨n, ?_, hc⟩
        rcases hr with rfl | rfl
        · exact Finset.mem_union_left _ (by simp [PhysicalForest.children, hp])
        · exact Finset.mem_union_right _ (by simp [PhysicalForest.children, hp])
      · simp [forcedRow, hp, hb, hk, hr] at he
  · intro hc
    obtain ⟨n, hn, hc⟩ := Finset.mem_image.mp hc
    rcases Finset.mem_union.mp hn with hn | hn
    all_goals
      have hp := (Finset.mem_filter.mp hn).2
      have nb : ¬ F.Binary R.H1 := fun hb => binary_not_unary F hb R.H1_unary
      have nk : ¬ F.Binary R.K1 := fun hb => binary_not_unary F hb R.K1_unary
      have dist : R.K ≠ R.H1 ∧ R.K ≠ R.K1 := by
        have hs := (List.pairwise_cons.mp (List.pairwise_cons.mp R.marked_distinct).2).1
        exact ⟨hs R.H1 (by simp), hs R.K1 (by simp)⟩
    · exact ⟨n, by simp [forcedRow, hp, nb, Ne.symm dist.1, hc]⟩
    · exact ⟨n, by simp [forcedRow, hp, nk, Ne.symm dist.2, hc]⟩

private theorem occupied_extra (i : Fin e) :
    occupied (e := e) F R (extraTarget F R i) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro c hc
  obtain ⟨n, hn⟩ := (Finset.mem_filter.mp hc).2
  cases hp : F.parent n with
  | none => simp [forcedRow, hp] at hn
  | some p =>
    unfold forcedRow at hn
    simp only [hp] at hn
    split_ifs at hn with hb hk hr
    · simp only [binaryTarget] at hn
      split_ifs at hn <;> cases hn
    · simp only [binaryTarget] at hn
      split_ifs at hn <;> cases hn
    · simp [resolvingTarget, extraTarget] at hn

/-- Q, every other binary target, Z and extras occupy exactly 3/2/2/0 digits.
This is source incidence data; it is independent of alpha and capacity. -/
theorem occupied_counts (q : Target (e := e) F R) :
    (occupied F R q).card = match q with
      | .inl b => if b.val = R.A then 3 else 2
      | .inr (.inl _) => 2
      | .inr (.inr _) => 0 := by
  cases q with
  | inl b =>
    rw [occupied_binary_image F R b]
    by_cases he : b.val = R.A
    · simpa [he] using R.shared_three
    · simp only [if_neg he, Finset.union_empty]
      rw [Finset.card_image_iff.mpr]
      · exact b.property.1
      · intro n hn m hm hc
        exact F.child_digit_injective b.val n m
          (Finset.mem_filter.mp hn).2 (Finset.mem_filter.mp hm).2 hc
  | inr t =>
    cases t with
    | inl u =>
      cases u
      change (occupied (e := e) F R (resolvingTarget F R)).card = 2
      rw [occupied_resolving F R]
      obtain ⟨n, hn⟩ := Finset.card_eq_one.mp R.H1_unary
      obtain ⟨m, hm⟩ := Finset.card_eq_one.mp R.K1_unary
      have hpn : F.parent n = some R.H1 := by
        have hmem : n ∈ F.children R.H1 := by rw [hn]; simp
        exact (Finset.mem_filter.mp hmem).2
      have hpm : F.parent m = some R.K1 := by
        have hmem : m ∈ F.children R.K1 := by rw [hm]; simp
        exact (Finset.mem_filter.mp hmem).2
      have colors := R.resolving_colors n m hpn hpm
      simp [hn, hm, colors]
    | inr i =>
      change (occupied (e := e) F R (extraTarget F R i)).card = 0
      rw [occupied_extra F R i]; rfl



/-- The three actual first digits give exactly three distinct history roots. -/
theorem root_count : (Finset.univ.image F.root).card = 3 := by
  rw [Finset.card_image_iff.mpr]
  · simp
  · intro a _ b _ he
    have hc := congrArg F.color he
    simpa only [F.root_color] using hc

/-- Complete original leaves correspond to the original fixed output labels. -/
noncomputable def leafEquiv : {n : Node // ¬ F.Internal n} ≃ Label P where
  toFun n := F.leafLabel n.val
  invFun x := ⟨F.event x (F.reads x - 1), by
    rintro ⟨m, hm⟩
    exact F.last x m (Finset.mem_filter.mp hm).2⟩
  left_inv n := by
    obtain ⟨x, hx⟩ := F.support_nonempty n.val
    obtain ⟨i, hi, he⟩ := F.support_events n.val x hx
    have label : F.leafLabel n.val = x := F.leaf_original n.val x hx (by
      intro m hp
      exact n.property ⟨m, by simp [PhysicalForest.children, hp]⟩)
    have final : i = F.reads x - 1 := by
      by_contra bad
      have more : i + 1 < F.reads x := by omega
      have hp := F.successor x i more
      rw [he] at hp
      exact n.property (child_internal F hp)
    apply Subtype.ext
    change F.event (F.leafLabel n.val) (F.reads (F.leafLabel n.val) - 1) = n.val
    rw [label, ← final, he]
  right_inv x := by
    have hi : F.reads x - 1 < F.reads x := by have := F.reads_pos x; omega
    exact F.leaf_original _ x (F.event_support x _ hi) (F.last x)

/-- Every original input supplies one leaf and no singleton continuation is
mistaken for a leaf. This count uses the complete, unpruned physical forest. -/
theorem leaf_count : Fintype.card {n : Node // ¬ F.Internal n} = 3 * P := by
  let : NeZero (3 * P) := ⟨by omega⟩
  rw [Fintype.card_congr (leafEquiv F)]
  exact ZMod.card (3 * P)

end D5.S3.ObserverMemory.Algorithms.FixedForestTargetInventory
