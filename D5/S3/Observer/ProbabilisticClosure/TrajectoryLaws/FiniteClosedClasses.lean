/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClasses
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteClosedClasses
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual terminal communicating classes and restrictions of a finite stochastic matrix. -/
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.SubstochasticEscape

open Finset Matrix
open scoped BigOperators
namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClasses
noncomputable section
universe u
variable {X : Type u}

/-- Reachability in the actual positive-transition support, including the empty path. -/
def Reach (P : Matrix X X ℝ) (x y : X) : Prop :=
  Nonempty (@Quiver.Path X P.toQuiver x y)

private theorem reach_refl (P : Matrix X X ℝ) (x : X) : Reach P x x :=
  ⟨@Quiver.Path.nil X P.toQuiver x⟩

private theorem reach_trans {P : Matrix X X ℝ} {x y z : X}
    (h : Reach P x y) (k : Reach P y z) : Reach P x z :=
  ⟨@Quiver.Path.comp X P.toQuiver x y z h.some k.some⟩

/-- A terminal state has no reachable state outside its communicating class. -/
def Terminal (P : Matrix X X ℝ) (x : X) : Prop :=
  ∀ y, Reach P x y → Reach P y x

variable [Fintype X]

/-- The actual communicating class of a state. -/
def communicatingClass (P : Matrix X X ℝ) (x : X) : Finset X := by
  classical
  exact univ.filter (fun y => Reach P x y ∧ Reach P y x)

/-- Actual closed classes, with duplicate representatives identified by equality of state sets. -/
abbrev ClosedClass (P : Matrix X X ℝ) :=
  {s : Finset X // ∃ x, Terminal P x ∧ s = communicatingClass P x}

/-- Recurrent states are precisely the union of the actual closed classes. -/
def Recurrent (P : Matrix X X ℝ) (x : X) : Prop :=
  ∃ C : ClosedClass P, x ∈ C.val

/-- The complement of the recurrent union. -/
abbrev Transient (P : Matrix X X ℝ) := {x : X // ¬ Recurrent P x}

/-- The actual restriction to a finite state set. -/
def restriction (P : Matrix X X ℝ) (s : Finset X) : Matrix s s ℝ :=
  P.submatrix Subtype.val Subtype.val

private theorem mem_class (P : Matrix X X ℝ) (x y : X) :
    y ∈ communicatingClass P x ↔ Reach P x y ∧ Reach P y x := by
  classical
  simp [communicatingClass]

omit [Fintype X] in
private theorem terminal_of_mem {P : Matrix X X ℝ} {x y : X}
    (hx : Terminal P x) (hxy : Reach P x y) : Terminal P y := by
  intro z hyz
  exact reach_trans (hx z (reach_trans hxy hyz)) hxy

/-- Every state reaches an actual terminal class, without a stochastic hypothesis. -/
private theorem reaches_closed_class (P : Matrix X X ℝ) (x : X) :
    ∃ C : ClosedClass P, ∃ y : C.val, Reach P x y.val := by
  classical
  let r (y : X) := univ.filter (Reach P y)
  have hm (a b : X) : b ∈ r a ↔ Reach P a b := by simp [r]
  have hr : (r x).Nonempty := ⟨x, (hm x x).mpr (reach_refl P x)⟩
  obtain ⟨y, hy, hmin⟩ := exists_min_image (r x) (fun y => (r y).card) hr
  have ht : Terminal P y := by
    intro z hyz
    have hz : z ∈ r x := (hm x z).mpr (reach_trans ((hm x y).mp hy) hyz)
    have hsub : r z ⊆ r y := fun w hw =>
      (hm y w).mpr (reach_trans hyz ((hm z w).mp hw))
    have heq : r z = r y := eq_of_subset_of_card_le hsub (hmin z hz)
    exact (hm z y).mp (heq.symm ▸ (hm y y).mpr (reach_refl P y))
  let C : ClosedClass P := ⟨communicatingClass P y, y, ht, rfl⟩
  exact ⟨C, ⟨y, (mem_class P y y).mpr ⟨reach_refl P y, reach_refl P y⟩⟩,
    (hm x y).mp hy⟩

/-- Nonempty closed classes, actual mutual reachability, and closure under all support paths. -/
private theorem closed_class_structure (P : Matrix X X ℝ) (C : ClosedClass P) :
    C.val.Nonempty ∧
    (∀ x ∈ C.val, ∀ y ∈ C.val, Reach P x y) ∧
    (∀ x ∈ C.val, ∀ y, Reach P x y → y ∈ C.val) := by
  obtain ⟨a, ha, he⟩ := C.property
  rw [he]
  refine ⟨⟨a, (mem_class P a a).mpr ⟨reach_refl P a, reach_refl P a⟩⟩, ?_, ?_⟩
  · intro x hx y hy
    exact reach_trans ((mem_class P a x).mp hx).2 ((mem_class P a y).mp hy).1
  · intro x hx y hxy
    have hay := reach_trans ((mem_class P a x).mp hx).1 hxy
    exact (mem_class P a y).mpr ⟨hay, ha y hay⟩

/-- Distinct actual closed classes are disjoint. -/
private theorem closed_classes_disjoint (P : Matrix X X ℝ) (C D : ClosedClass P)
    (hne : C ≠ D) : Disjoint C.val D.val := by
  classical
  apply disjoint_left.mpr
  intro z hzC hzD
  apply hne
  apply Subtype.ext
  ext w
  constructor
  · intro hw
    exact (closed_class_structure P D).2.2 z hzD w
      ((closed_class_structure P C).2.1 z hzC w hw)
  · intro hw
    exact (closed_class_structure P C).2.2 z hzC w
      ((closed_class_structure P D).2.1 z hzD w hw)

/-- The recurrent union has exactly the terminal states. -/
private theorem recurrent_iff_terminal (P : Matrix X X ℝ) (x : X) :
    Recurrent P x ↔ Terminal P x := by
  constructor
  · rintro ⟨C, hx⟩
    obtain ⟨a, ha, he⟩ := C.property
    rw [he, mem_class] at hx
    exact terminal_of_mem ha hx.1
  · intro hx
    exact ⟨⟨communicatingClass P x, x, hx, rfl⟩,
      (mem_class P x x).mpr ⟨reach_refl P x, reach_refl P x⟩⟩

private theorem recurrent_closed {P : Matrix X X ℝ} {x y : X}
    (hx : Recurrent P x) (hxy : Reach P x y) : Recurrent P y := by
  obtain ⟨C, hx⟩ := hx
  exact ⟨C, (closed_class_structure P C).2.2 x hx y hxy⟩

/-- A nonempty ambient state type yields an actual closed class. -/
private theorem closed_class_nonempty (P : Matrix X X ℝ) [Nonempty X] :
    Nonempty (ClosedClass P) := by
  obtain ⟨C, _⟩ := reaches_closed_class P (Classical.arbitrary X)
  exact ⟨C⟩

/-- Class state cardinality lies between one and the ambient cardinality. -/
private theorem class_card_bounds (P : Matrix X X ℝ) (C : ClosedClass P) :
    0 < Fintype.card C.val ∧ Fintype.card C.val ≤ Fintype.card X := by
  classical
  simpa using And.intro (card_pos.mpr (closed_class_structure P C).1)
    (card_le_card (subset_univ C.val))

variable [DecidableEq X]

private theorem reach_iff_pow {P : Matrix X X ℝ} (hP : ∀ x y, 0 ≤ P x y) (x y : X) :
    Reach P x y ↔ ∃ n, 0 < (P ^ n) x y := by
  let := P.toQuiver
  constructor
  · rintro ⟨p⟩
    exact ⟨p.length, (Matrix.pow_apply_pos_iff_nonempty_path hP _ _ _).mpr ⟨p, rfl⟩⟩
  · rintro ⟨n, hn⟩
    obtain ⟨p, _⟩ := (Matrix.pow_apply_pos_iff_nonempty_path hP n x y).mp hn
    exact ⟨p⟩

private theorem pow_zero_of_closed (P : Matrix X X ℝ) (hP : ∀ x y, 0 ≤ P x y)
    (s : Finset X) (hs : ∀ x ∈ s, ∀ y, Reach P x y → y ∈ s)
    (n : ℕ) (x : X) (hx : x ∈ s) (y : X) (hy : y ∉ s) : (P ^ n) x y = 0 := by
  apply le_antisymm _ (Matrix.pow_apply_nonneg hP n x y)
  apply le_of_not_gt
  intro hp
  exact hy (hs x hx y ((reach_iff_pow hP x y).mpr ⟨n, hp⟩))

/-- Closed restriction powers are exactly the ambient powers on the actual subtype. -/
private theorem closed_restriction_pow (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X)
    (C : ClosedClass P) (n : ℕ) (x y : C.val) :
    (restriction P C.val ^ n) x y = (P ^ n) x.val y.val := by
  classical
  induction n generalizing x y with
  | zero =>
    by_cases h : x = y
    · subst y; simp
    · have hv : x.val ≠ y.val := fun he => h (Subtype.ext he)
      simp [h, hv]
  | succ n ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    calc
      ∑ k : C.val, (restriction P C.val ^ n) x k * restriction P C.val k y =
        ∑ k : C.val, (P ^ n) x.val k.val * P k.val y.val := by
          apply sum_congr rfl
          intro k _
          rw [ih]
          rfl
      _ = ∑ k ∈ C.val, (P ^ n) x.val k * P k y.val :=
        Finset.sum_coe_sort C.val (fun k : X => (P ^ n) x.val k * P k y.val)
      _ = ∑ k, (P ^ n) x.val k * P k y.val := by
        apply sum_subset (subset_univ _)
        intro k _ hk
        rw [pow_zero_of_closed P hP.1 C.val (closed_class_structure P C).2.2 n
          x.val x.property k hk, zero_mul]

/-- The actual closed restriction is row stochastic. -/
private theorem closed_restriction_stochastic (P : Matrix X X ℝ)
    (hP : P ∈ rowStochastic ℝ X) (C : ClosedClass P) :
    restriction P C.val ∈ rowStochastic ℝ C.val := by
  classical
  apply mem_rowStochastic_iff_sum.mpr
  refine ⟨fun x y => hP.1 x.val y.val, fun x => ?_⟩
  change ∑ y : C.val, P x.val y.val = 1
  rw [Finset.sum_coe_sort C.val]
  calc
    ∑ y ∈ C.val, P x.val y = ∑ y, P x.val y := by
      apply sum_subset (subset_univ _)
      intro y _ hy
      simpa using pow_zero_of_closed P hP.1 C.val (closed_class_structure P C).2.2 1
        x.val x.property y hy
    _ = 1 := sum_row_of_mem_rowStochastic hP x.val


local instance (P : Matrix X X ℝ) : DecidablePred (Recurrent P) := Classical.decPred _
noncomputable instance (P : Matrix X X ℝ) : Fintype (ClosedClass P) := Fintype.ofFinite _

/-- The exact killed restriction to the complement of all actual closed classes. -/
def transientMatrix (P : Matrix X X ℝ) : Matrix (Transient P) (Transient P) ℝ :=
  P.submatrix Subtype.val Subtype.val

private theorem closed_irreducible (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X)
    (C : ClosedClass P) : IsIrreducible (restriction P C.val) := by
  classical
  have hs := closed_restriction_stochastic P hP C
  apply (Matrix.isIrreducible_iff_exists_pow_pos hs.1).mpr
  intro x y
  obtain ⟨t, _, ht⟩ := (sum_pos_iff_of_nonneg (fun t _ => hs.1 x t)).mp
    (by rw [sum_row_of_mem_rowStochastic hs x]; norm_num)
  obtain ⟨n, hn⟩ := (reach_iff_pow hP.1 t.val y.val).mp
    ((closed_class_structure P C).2.1 t.val t.property y.val y.property)
  refine ⟨n + 1, Nat.succ_pos _, ?_⟩
  rw [closed_restriction_pow P hP C, pow_succ', Matrix.mul_apply]
  apply (sum_pos_iff_of_nonneg (fun k _ =>
    mul_nonneg (hP.1 x.val k) (Matrix.pow_apply_nonneg hP.1 n k y.val))).mpr
  exact ⟨t.val, mem_univ _, mul_pos ht hn⟩

private theorem transient_pow (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X)
    (n : ℕ) (x y : Transient P) :
    (transientMatrix P ^ n) x y = (P ^ n) x.val y.val := by
  classical
  induction n generalizing x y with
  | zero =>
    by_cases h : x = y
    · subst y; simp
    · have hv : x.val ≠ y.val := fun he => h (Subtype.ext he)
      simp [h, hv]
  | succ n ih =>
    rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
    calc
      ∑ k : Transient P, transientMatrix P x k * (transientMatrix P ^ n) k y =
          ∑ k : Transient P, P x.val k.val * (P ^ n) k.val y.val := by
        apply sum_congr rfl
        intro k _
        rw [ih]
        rfl
      _ = ∑ k ∈ univ.filter (fun k => ¬ Recurrent P k),
          P x.val k * (P ^ n) k y.val :=
        (Finset.sum_subtype (p := fun k => ¬ Recurrent P k)
          (univ.filter (fun k => ¬ Recurrent P k)) (fun _ => by simp)
          (fun k => P x.val k * (P ^ n) k y.val)).symm
      _ = ∑ k, P x.val k * (P ^ n) k y.val := by
        apply sum_subset (filter_subset _ _)
        intro k _ hk
        have hkr : Recurrent P k := by simpa using hk
        have hz : (P ^ n) k y.val = 0 := by
          apply le_antisymm _ (Matrix.pow_apply_nonneg hP.1 n k y.val)
          apply le_of_not_gt
          intro hp
          exact y.property (recurrent_closed hkr
            ((reach_iff_pow hP.1 k y.val).mpr ⟨n, hp⟩))
        rw [hz, mul_zero]

private theorem transient_substochastic (P : Matrix X X ℝ)
    (hP : P ∈ rowStochastic ℝ X) :
    SubstochasticEscape.IsSubstochastic (transientMatrix P) := by
  classical
  refine ⟨fun x y => hP.1 x.val y.val, fun x => ?_⟩
  change ∑ y : Transient P, P x.val y.val ≤ 1
  have hsplit := Fintype.sum_subtype_add_sum_subtype (Recurrent P) (P x.val)
  have hn : 0 ≤ ∑ y : {y // Recurrent P y}, P x.val y.val :=
    sum_nonneg fun _ _ => hP.1 _ _
  rw [sum_row_of_mem_rowStochastic hP x.val] at hsplit
  linarith

private theorem transient_row_strict (P : Matrix X X ℝ)
    (hP : P ∈ rowStochastic ℝ X) (x : Transient P) :
    ∃ n, 0 < n ∧ SubstochasticEscape.rowSum (transientMatrix P) n x < 1 := by
  classical
  obtain ⟨C, y, hxy⟩ := reaches_closed_class P x.val
  have hyr : Recurrent P y.val := ⟨C, y.property⟩
  obtain ⟨n, hn⟩ := (reach_iff_pow hP.1 x.val y.val).mp hxy
  have hnp : 0 < n := by
    by_contra! he
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hn
    have hne : x.val ≠ y.val := fun he => x.property (he ▸ hyr)
    simp [hne] at hn
  refine ⟨n, hnp, ?_⟩
  have hp := (rowStochastic ℝ X).pow_mem hP n
  have hsplit := Fintype.sum_subtype_add_sum_subtype (Recurrent P) ((P ^ n) x.val)
  have hrec : 0 < ∑ z : {z // Recurrent P z}, (P ^ n) x.val z.val :=
    (sum_pos_iff_of_nonneg (fun z _ => hp.1 _ _)).mpr
      ⟨⟨y.val, hyr⟩, mem_univ _, hn⟩
  have heq : SubstochasticEscape.rowSum (transientMatrix P) n x =
      ∑ z : Transient P, (P ^ n) x.val z.val := by
    unfold SubstochasticEscape.rowSum
    exact sum_congr rfl fun z _ => transient_pow P hP n x z
  rw [sum_row_of_mem_rowStochastic hp x.val] at hsplit
  rw [heq]
  linarith

private theorem transient_escape (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X) :
    ∃ h : ℕ, ∃ c : ℝ, 0 < h ∧ c < 1 ∧
      ∀ x, SubstochasticEscape.rowSum (transientMatrix P) h x ≤ c := by
  classical
  by_cases hu : Nonempty (Transient P)
  · let := hu
    let n : Transient P → ℕ := fun x => (transient_row_strict P hP x).choose
    have hn (x) : 0 < n x ∧
        SubstochasticEscape.rowSum (transientMatrix P) (n x) x < 1 :=
      (transient_row_strict P hP x).choose_spec
    obtain ⟨a, _, ha⟩ := exists_max_image (univ : Finset (Transient P)) n univ_nonempty
    let h := n a
    have hh (x : Transient P) :
        SubstochasticEscape.rowSum (transientMatrix P) h x < 1 :=
      lt_of_le_of_lt ((transient_substochastic P hP).rowSum_antitone x
        (ha x (mem_univ _))) (hn x).2
    obtain ⟨b, _, hb⟩ := exists_max_image (univ : Finset (Transient P))
      (SubstochasticEscape.rowSum (transientMatrix P) h) univ_nonempty
    exact ⟨h, SubstochasticEscape.rowSum (transientMatrix P) h b,
      (hn a).1, hh b, fun x => hb x (mem_univ _)⟩
  · let : IsEmpty (Transient P) := not_nonempty_iff.mp hu
    exact ⟨1, 0, by norm_num, by norm_num, fun x => isEmptyElim x⟩


omit [DecidableEq X] in
private theorem partition_card (P : Matrix X X ℝ) :
    (∑ C : ClosedClass P, Fintype.card C.val) + Fintype.card (Transient P) =
      Fintype.card X := by
  classical
  have hd : (↑(univ : Finset (ClosedClass P)) : Set (ClosedClass P)).PairwiseDisjoint
      (fun C => C.val) := by
    intro C _ D _ hne
    exact closed_classes_disjoint P C D hne
  have hu : (univ : Finset (ClosedClass P)).biUnion (fun C => C.val) =
      univ.filter (Recurrent P) := by
    ext x
    simp [Recurrent]
  have hc : (univ.filter (Recurrent P)).card =
      ∑ C : ClosedClass P, Fintype.card C.val := by
    rw [← hu, card_biUnion hd]
    simp
  have ht : (univ.filter (fun x => ¬ Recurrent P x)).card =
      Fintype.card (Transient P) := by
    symm
    exact Fintype.card_of_subtype _ (by simp)
  have he := card_filter_add_card_filter_not (s := (univ : Finset X)) (Recurrent P)
  rw [hc, ht, card_univ] at he
  exact he

omit [DecidableEq X] in
private theorem class_count_bound (P : Matrix X X ℝ) :
    Fintype.card (ClosedClass P) ≤ Fintype.card X := by
  classical
  have hsum : Fintype.card (ClosedClass P) ≤
      ∑ C : ClosedClass P, Fintype.card C.val := by
    calc
      _ = ∑ _C : ClosedClass P, 1 := by simp
      _ ≤ _ := sum_le_sum fun C _ => (class_card_bounds P C).1
  have hc := partition_card P
  omega

/-- Complete structural interface derived from the matrix, without supplied class certificates. -/
structure Structure (P : Matrix X X ℝ) : Prop where
  class_count : Fintype.card (ClosedClass P) ≤ Fintype.card X
  partition_card : (∑ C : ClosedClass P, Fintype.card C.val) +
    Fintype.card (Transient P) = Fintype.card X
  class_scc : ∀ C : ClosedClass P, ∃ a ∈ C.val, ∀ y,
    y ∈ C.val ↔
      @Quiver.StronglyConnectedComponent.mk X P.toQuiver a =
      @Quiver.StronglyConnectedComponent.mk X P.toQuiver y
  class_nonempty : ∀ C : ClosedClass P, C.val.Nonempty
  class_closed : ∀ C : ClosedClass P, ∀ x ∈ C.val, ∀ y,
    Reach P x y → y ∈ C.val
  class_communicates : ∀ C : ClosedClass P, ∀ x ∈ C.val, ∀ y ∈ C.val, Reach P x y
  class_irreducible : ∀ C : ClosedClass P, IsIrreducible (restriction P C.val)
  class_stochastic : ∀ C : ClosedClass P, restriction P C.val ∈ rowStochastic ℝ C.val
  class_powers : ∀ C : ClosedClass P, ∀ n (x y : C.val),
    (restriction P C.val ^ n) x y = (P ^ n) x.val y.val
  class_no_exit : ∀ C : ClosedClass P, ∀ n (x : C.val) y,
    y ∉ C.val → (P ^ n) x.val y = 0
  class_paths : ∀ C : ClosedClass P, ∀ n (x y : C.val),
    0 < (restriction P C.val ^ n) x y ↔
      Nonempty {p : @Quiver.Path X P.toQuiver x.val y.val //
        @Quiver.Path.length X P.toQuiver x.val y.val p = n}
  disjoint : ∀ C D : ClosedClass P, C ≠ D → Disjoint C.val D.val
  class_card : ∀ C : ClosedClass P,
    0 < Fintype.card C.val ∧ Fintype.card C.val ≤ Fintype.card X
  recurrent_terminal : ∀ x, Recurrent P x ↔ Terminal P x
  reaches_class : ∀ x, ∃ C : ClosedClass P, ∃ y : C.val, Reach P x y.val
  ambient_nonempty : Nonempty X → Nonempty (ClosedClass P)
  transient_powers : ∀ n (x y : Transient P),
    (transientMatrix P ^ n) x y = (P ^ n) x.val y.val
  transient_paths : ∀ n (x y : Transient P),
    0 < (transientMatrix P ^ n) x y ↔
      Nonempty {p : @Quiver.Path X P.toQuiver x.val y.val //
        @Quiver.Path.length X P.toQuiver x.val y.val p = n}
  empty_ambient : IsEmpty X → IsEmpty (ClosedClass P)
  empty_transient : IsEmpty (Transient P) →
    transientMatrix P = 0 ∧ (1 - transientMatrix P).det = 1 ∧
      (∀ x, SubstochasticEscape.rowSum (transientMatrix P) 1 x ≤ 0)
  substochastic : SubstochasticEscape.IsSubstochastic (transientMatrix P)
  escape : ∃ h : ℕ, ∃ c : ℝ, 0 < h ∧ c < 1 ∧
    ∀ x, SubstochasticEscape.rowSum (transientMatrix P) h x ≤ c
  transient_decay : ∀ x y : Transient P,
    Filter.Tendsto (fun n : ℕ => (transientMatrix P ^ n) x y) Filter.atTop (nhds 0)
  transient_nonsingular : (1 - transientMatrix P).det ≠ 0

/-- Actual finite stochastic-chain structure and uniform transient escape. -/
theorem actual_structure (P : Matrix X X ℝ) (hP : P ∈ rowStochastic ℝ X) :
    Structure P := by
  classical
  have hQ := transient_substochastic P hP
  obtain ⟨h, c, hh, hc, hb⟩ := transient_escape P hP
  refine {
    class_count := class_count_bound P
    partition_card := partition_card P
    class_scc := ?_
    class_nonempty := fun C => (closed_class_structure P C).1
    class_closed := fun C => (closed_class_structure P C).2.2
    class_communicates := fun C => (closed_class_structure P C).2.1
    class_irreducible := closed_irreducible P hP
    class_stochastic := closed_restriction_stochastic P hP
    class_powers := closed_restriction_pow P hP
    class_no_exit := fun C n x y hy => pow_zero_of_closed P hP.1 C.val
      (closed_class_structure P C).2.2 n x.val x.property y hy
    class_paths := fun C n x y => by
      rw [closed_restriction_pow P hP C]
      exact Matrix.pow_apply_pos_iff_nonempty_path hP.1 n x.val y.val
    disjoint := closed_classes_disjoint P
    class_card := class_card_bounds P
    recurrent_terminal := recurrent_iff_terminal P
    reaches_class := reaches_closed_class P
    ambient_nonempty := fun hx => @closed_class_nonempty X _ P hx
    transient_powers := transient_pow P hP
    transient_paths := fun n x y => by
      rw [transient_pow P hP n]
      exact Matrix.pow_apply_pos_iff_nonempty_path hP.1 n x.val y.val
    empty_ambient := ?_
    empty_transient := ?_
    substochastic := hQ
    escape := ⟨h, c, hh, hc, hb⟩
    transient_decay := fun x y => hQ.tendsto_pow_entry hh hc hb x y
    transient_nonsingular := hQ.det_one_sub_ne_zero hh hc hb }
  · intro C
    obtain ⟨a, ha, he⟩ := C.property
    refine ⟨a, ?_, fun y => ?_⟩
    · rw [he]
      exact (mem_class P a a).mpr ⟨reach_refl P a, reach_refl P a⟩
    · rw [he, mem_class]
      exact (@Quiver.StronglyConnectedComponent.eq X P.toQuiver a y).symm
  · intro hx
    let := hx
    exact ⟨fun C => isEmptyElim (closed_class_structure P C).1.choose⟩
  · intro hu
    let := hu
    have hz : transientMatrix P = 0 := by ext x; exact isEmptyElim x
    exact ⟨hz, by simp, fun x => isEmptyElim x⟩

end
end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteClosedClasses
