/- GID: D5/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGeometry/ProjectivePlaneGoodOrdering
   mirror-E: none(waiver:symbolic-arbitrary-plane-proof)
   anchors: []
   utility: none
   digest: Original line-avoiding orders and literal Good on exact projective-plane quotients. -/

import D5.S3.Geometry.FiniteGeometry.ProjectivePlaneIntegerLattice
import D5.S3.Combinatorics.Permutation.ForbiddenContiguousBlocks
import D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
Every point and line is original and arbitrary. The derived order is q>=2.
The live new count is n*(q+1)!*(n-q)!, strictly less than n! for q>=3.
At q=2 equality is repaired by a real order with two intersecting line blocks.
No classification, finite plane census, torsion cancellation or probabilistic
independence assumption occurs. The native supplied proof, Sections 6-7,
guides this implementation; only actual compiled Lean terms establish it.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
open Finset Configuration
open D5.S3.Combinatorics.CircularWords.DisjointBlockContraction
open D5.S3.Combinatorics.Permutation.ForbiddenContiguousBlocks
open D5.S3.Combinatorics.Sequenceability.PairedZeroSubsetSpectrum

namespace D5.S3.Geometry.FiniteGeometry.ProjectivePlaneGoodOrdering

variable {P L : Type*} [Membership P L] [Fintype P] [Fintype L] [ProjectivePlane P L]

private abbrev q : ℕ := ProjectivePlane.order P L

/-- The actual original support of a line. -/
def lineSupport (l : L) : Finset P := univ.filter (· ∈ l)

private theorem support_card (l : L) : (lineSupport (P := P) l).card = q (P := P) (L := L) + 1 := by
  have h := ProjectivePlane.pointCount_eq P l
  rw [pointCount, Nat.card_eq_fintype_card, Fintype.card_subtype] at h
  simpa [lineSupport, q] using h

private theorem support_nonempty (l : L) : (lineSupport (P := P) l).Nonempty := by
  apply card_pos.mp
  rw [support_card]
  omega

private theorem line_meets (l k : L) : ∃ x : P, x ∈ l ∧ x ∈ k := by
  by_cases h : l = k
  · subst k
    obtain ⟨x, hx⟩ := support_nonempty (P := P) l
    have hx' : x ∈ l := by simpa [lineSupport] using hx
    exact ⟨x, hx', hx'⟩
  · obtain ⟨x, hx, _⟩ := HasPoints.existsUnique_point P L l k h
    exact ⟨x, hx⟩

private theorem support_intersection {l k : L} (h : l ≠ k) :
    ∃ p : P, lineSupport (P := P) l ∩ lineSupport k = {p} := by
  obtain ⟨p, hp, hu⟩ := HasPoints.existsUnique_point P L l k h
  refine ⟨p, ?_⟩
  ext x
  simp only [lineSupport, mem_inter, mem_filter, mem_univ, true_and, mem_singleton]
  exact ⟨hu x, fun he => he ▸ hp⟩

private theorem choose_increasing {n r s : ℕ} (hrs : r ≤ s) (hh : s ≤ n / 2) :
    n.choose r ≤ n.choose s := by
  have aux : ∀ t, r ≤ t → t ≤ n / 2 → n.choose r ≤ n.choose t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => intro _; exact le_rfl
    | succ t ht ih =>
      intro hh
      exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))
  exact aux s hrs hh

private theorem plane_count_strict (d : ℕ) (hd : 3 ≤ d) :
    (d^2+d+1) * (d+1).factorial *
      (d^2+d+1-(d+1)+1).factorial < (d^2+d+1).factorial := by
  let n := d^2+d+1
  change n * (d+1).factorial * (n-(d+1)+1).factorial < n.factorial
  have hd2 : 9 ≤ d*d := Nat.mul_le_mul hd hd
  have hn : 13 ≤ n := by dsimp [n]; nlinarith
  have hdn : 2*d ≤ n := by dsimp [n]; nlinarith
  have hh : d ≤ n/2 := by omega
  have hmono := choose_increasing hd hh
  have h3 : 6 * n.choose 3 = n*(n-1)*(n-2) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose n 3
    norm_num [Nat.descFactorial] at h
    nlinarith [h]
  have hsub : n-1 = d*(d+1) := by
    have : n = d*(d+1)+1 := by dsimp [n]; ring
    omega
  have ha : 6 < d*(n-2) := by
    have hm := Nat.mul_le_mul hd (show 11 ≤ n-2 by omega)
    nlinarith
  have hm := Nat.mul_lt_mul_of_pos_left ha (show 0 < n*(d+1) by positivity)
  have hp : 6*(n*(d+1)) < n*(n-1)*(n-2) := by rw [hsub]; nlinarith [hm]
  have hc3 : n*(d+1) < n.choose 3 := by omega
  have hc : n*(d+1) < n.choose d := hc3.trans_le hmono
  have hf := Nat.choose_mul_factorial_mul_factorial (show d ≤ n by omega)
  have hm' := Nat.mul_lt_mul_of_pos_right hc
    (Nat.mul_pos (Nat.factorial_pos d) (Nat.factorial_pos (n-d)))
  have he : n-(d+1)+1 = n-d := by omega
  rw [he, Nat.factorial_succ]
  nlinarith [hf, hm']

/-- Every actual finite nondegenerate projective plane has an order of ALL
original points containing no original line as a contiguous interval. -/
theorem exists_line_avoiding_order : ∃ w ∈ orders (univ : Finset P),
    ∀ l : L, ¬ Block (lineSupport l) w := by
  have hq : 2 ≤ q (P := P) (L := L) := by
    exact ProjectivePlane.one_lt_order P L
  have hi : (∑ l : L, (lineSupport (P := P) l).card.factorial *
      ((univ : Finset P).card - (lineSupport l).card + 1).factorial) =
      (q (P := P) (L := L)^2 + q (P := P) (L := L) + 1) *
        (q (P := P) (L := L)+1).factorial *
        (q (P := P) (L := L)^2+q (P := P) (L := L)+1-
          (q (P := P) (L := L)+1)+1).factorial := by
    simp [support_card, ProjectivePlane.card_points P L, ProjectivePlane.card_lines P L,
      q, Nat.mul_assoc]
  apply exists_avoiding univ (lineSupport (P := P) (L := L)) (by intros; exact subset_univ _)
    (fun l => support_nonempty l)
  by_cases he : q (P := P) (L := L) = 2
  · right
    constructor
    · rw [hi, card_univ, ProjectivePlane.card_points P L]
      change _ ≤ (q (P := P) (L := L)^2+q (P := P) (L := L)+1).factorial
      norm_num [he]
    · have hc : 1 < (univ : Finset L).card := by
        rw [card_univ, ProjectivePlane.card_lines P L]
        change 1 < q (P := P) (L := L)^2+q (P := P) (L := L)+1
        nlinarith
      obtain ⟨l, _, k, _, hlk⟩ := one_lt_card.mp hc
      obtain ⟨p, hp⟩ := support_intersection (P := P) hlk
      obtain ⟨w, hw, hs, ht⟩ := two_intersecting_blocks univ
        (lineSupport (P := P) l) (lineSupport k) (subset_univ _) (subset_univ _) p hp
      exact ⟨w, hw, l, k, hlk, hs, ht⟩
  · left
    rw [hi, card_univ, ProjectivePlane.card_points P L]
    exact plane_count_strict _ (by omega)


/-- Indexed Good depends on Boolean supports, even when label values repeat. -/
private theorem good_map_of_avoiding {X G I : Type*} [DecidableEq X] [AddCommGroup G]
    (A : Finset X) (a : X → G) (H : I → Finset X)
    (hz : ∀ S ⊆ A, S.Nonempty → S ≠ A → (∑ x ∈ S, a x) = 0 → ∃ t, S = H t)
    {w : List X} (hw : w.Perm A.toList) (ha : ∀ t, ¬ Block (H t) w) :
    Good (w.map a) := by
  intro i j hij hj hp hzero
  have hj' : j ≤ w.length := by simpa using hj
  have hp' : i ≠ 0 ∨ j ≠ w.length := by simpa using hp
  let u := (w.drop i).take (j-i)
  let S := u.toFinset
  have hn := hw.nodup_iff.mpr A.nodup_toList
  have hnu : u.Nodup := by
    dsimp [u]
    exact hn.drop.take
  have hul : u.length = j-i := by
    dsimp [u]
    rw [List.length_take, List.length_drop, Nat.min_eq_left (by omega)]
  have hsc : S.card = j-i := by
    rw [List.toFinset_card_of_nodup hnu]
    exact hul
  have hwl : w.length = A.card := by simpa using hw.length_eq
  have hsub : S ⊆ A := by
    intro x hx
    have hx' : x ∈ w := List.mem_of_mem_drop
      (List.mem_of_mem_take (List.mem_toFinset.mp hx))
    exact mem_toList.mp (hw.mem_iff.mp hx')
  have hne : S.Nonempty := card_pos.mp (by rw [hsc]; omega)
  have hproper : S ≠ A := by
    intro he
    have hc := congrArg Finset.card he
    rw [hsc, ← hwl] at hc
    omega
  have hu : u.Perm S.toList := by
    apply (List.perm_ext_iff_of_nodup hnu S.nodup_toList).mpr
    intro x
    simp [S]
  have hsum : (u.map a).sum = ∑ x ∈ S, a x := by simpa using (hu.map a).sum_eq
  have hzu : (u.map a).sum = 0 := by
    simpa [u, List.map_take, List.map_drop] using hzero
  obtain ⟨t, ht⟩ := hz S hsub hne hproper (hsum.symm.trans hzu)
  apply ha t
  refine ⟨w.take i, u, (w.drop i).drop (j-i), ?_, ?_⟩
  · dsimp [u]
    rw [List.append_assoc, List.take_append_drop, List.take_append_drop]
  · rw [← ht]
    exact hu

/-- The COMPLETE inclusion-minimal nonempty proper zero supports. -/
def MinimalZero {G : Type*} [AddCommGroup G] (a : P → G) (S : Finset P) : Prop :=
  S.Nonempty ∧ S ≠ univ ∧ (∑ x ∈ S, a x) = 0 ∧
    ∀ T : Finset P, T ⊂ S → T.Nonempty → (∑ x ∈ T, a x) ≠ 0

private theorem exists_minimal_zero {G : Type*} [AddCommGroup G] (a : P → G)
    (S : Finset P) (hne : S.Nonempty) (hp : S ≠ univ) (hz : (∑ x ∈ S, a x) = 0) :
    ∃ H : Finset P, H ⊆ S ∧ MinimalZero a H := by
  let F := S.powerset.filter (fun H => H.Nonempty ∧ (∑ x ∈ H, a x) = 0)
  have hF : F.Nonempty := ⟨S, by simp [F, hne, hz]⟩
  obtain ⟨H, hH, hmin⟩ := F.exists_min_image Finset.card hF
  have hHH := mem_filter.mp hH
  have hHS : H ⊆ S := mem_powerset.mp hHH.1
  refine ⟨H, hHS, hHH.2.1, ?_, hHH.2.2, ?_⟩
  · intro he
    exact hp (eq_univ_of_forall (fun x => hHS (he ▸ mem_univ x)))
  · intro T hT ht htz
    have hTF : T ∈ F := mem_filter.mpr
      ⟨mem_powerset.mpr (hT.1.trans hHS), ht, htz⟩
    exact (not_le_of_gt (card_lt_card hT)) (hmin T hTF)

/-- Completeness of the minimal rows implies completeness of ALL proper zero supports.
Removing one minimal zero row leaves a zero remainder; a second minimal row
would be a disjoint original line, contradicting actual line intersection. -/
theorem zero_support_iff_line_of_complete_minimals {G : Type*} [AddCommGroup G]
    (a : P → G) (hm : ∀ S : Finset P, MinimalZero a S ↔ ∃ l : L, S = lineSupport l)
    (S : Finset P) (hne : S.Nonempty) (hp : S ≠ univ) :
    (∑ x ∈ S, a x) = 0 ↔ ∃ l : L, S = lineSupport l := by
  constructor
  · intro hz
    obtain ⟨H, hHS, hH⟩ := exists_minimal_zero a S hne hp hz
    obtain ⟨l, hl⟩ := (hm H).mp hH
    by_cases he : H = S
    · exact ⟨l, he ▸ hl⟩
    have hstrict : H ⊂ S := lt_of_le_of_ne hHS he
    have hrne : (S \ H).Nonempty := sdiff_nonempty_of_card_lt_card (card_lt_card hstrict)
    have hrp : S \ H ≠ univ := by
      intro hr
      exact hp (eq_univ_of_forall (fun x => sdiff_subset (hr ▸ mem_univ x)))
    have hrz : (∑ x ∈ S \ H, a x) = 0 := by
      rw [sum_sdiff_eq_sub hHS, hz, hH.2.2.1, sub_self]
    obtain ⟨K, hKR, hK⟩ := exists_minimal_zero a (S \ H) hrne hrp hrz
    obtain ⟨k, hk⟩ := (hm K).mp hK
    obtain ⟨x, hxl, hxk⟩ := line_meets (P := P) l k
    have hxH : x ∈ H := by rw [hl]; simp [lineSupport, hxl]
    have hxK : x ∈ K := by rw [hk]; simp [lineSupport, hxk]
    exact ((mem_sdiff.mp (hKR hxK)).2 hxH).elim
  · intro h
    exact ((hm S).mpr h).2.2.1

/-- Literal original Good from the COMPLETE minimal-zero-line contract.
The word keeps every original index once; no injectivity of its labels is assumed.
These hypotheses also force the full original total to be nonzero. -/
theorem good_of_complete_minimals {G : Type*} [AddCommGroup G] (a : P → G)
    (hm : ∀ S : Finset P, MinimalZero a S ↔ ∃ l : L, S = lineSupport l) :
    (∑ x : P, a x) ≠ 0 ∧
      ∃ w : List P, w.Perm (univ : Finset P).toList ∧ Good (w.map a) := by
  constructor
  · intro hz
    have hc : 0 < (univ : Finset L).card := by
      rw [card_univ, ProjectivePlane.card_lines P L]
      positivity
    obtain ⟨l, _⟩ := card_pos.mp hc
    have hlz : (∑ x ∈ lineSupport (P := P) l, a x) = 0 :=
      ((hm _).mpr ⟨l, rfl⟩).2.2.1
    obtain ⟨y, hy⟩ := Nondegenerate.exists_point (P := P) l
    have hrne : (univ \ lineSupport (P := P) l).Nonempty := ⟨y, by simp [lineSupport, hy]⟩
    have hrp : univ \ lineSupport (P := P) l ≠ univ := by
      obtain ⟨x, hx⟩ := support_nonempty (P := P) l
      intro he
      have hh : x ∈ univ \ lineSupport (P := P) l :=
        (Finset.ext_iff.mp he x).mpr (mem_univ x)
      exact (mem_sdiff.mp hh).2 hx
    have hrz : (∑ x ∈ univ \ lineSupport (P := P) l, a x) = 0 := by
      rw [sum_sdiff_eq_sub (subset_univ _), hz, hlz, sub_self]
    obtain ⟨k, hk⟩ := (zero_support_iff_line_of_complete_minimals a hm _ hrne hrp).mp hrz
    obtain ⟨x, hxl, hxk⟩ := line_meets (P := P) l k
    have hh : x ∈ univ \ lineSupport (P := P) l := by rw [hk]; simp [lineSupport, hxk]
    exact (mem_sdiff.mp hh).2 (by simp [lineSupport, hxl])
  · obtain ⟨w, hw, ha⟩ := exists_line_avoiding_order (P := P) (L := L)
    refine ⟨w, mem_orders.mp hw, ?_⟩
    apply good_map_of_avoiding univ a (lineSupport (P := P) (L := L))
      (fun S _ hne hp hz => (zero_support_iff_line_of_complete_minimals a hm S hne hp).mp hz)
      (mem_orders.mp hw) ha

/-- Incidence is an actual additive homomorphism on original integer potentials. -/
def incidenceHom : (L → ℤ) →+ (P → ℤ) where
  toFun := ProjectivePlaneIntegerLattice.incidence
  map_zero' := by ext x; simp [ProjectivePlaneIntegerLattice.incidence]
  map_add' := by
    intro a b
    ext x
    simp [ProjectivePlaneIntegerLattice.incidence, mul_add, sum_add_distrib]

/-- The exact additive integer image, without saturation or extra relators. -/
def integerImage : AddSubgroup (P → ℤ) := (incidenceHom (P := P) (L := L)).range

/-- The actual universal original-coordinate quotient Z^P/im_Z F. -/
abbrev Universal := (P → ℤ) ⧸ integerImage (P := P) (L := L)

/-- The quotient class of an original unit, not a relabelled surrogate. -/
def label (x : P) : Universal (P := P) (L := L) :=
  QuotientAddGroup.mk' (integerImage (P := P) (L := L)) (ProjectivePlaneIntegerLattice.unit x)

private theorem unit_sum (S : Finset P) :
    (∑ x ∈ S, ProjectivePlaneIntegerLattice.unit x) = ProjectivePlaneIntegerLattice.indicator S := by
  ext y
  simp [ProjectivePlaneIntegerLattice.unit, ProjectivePlaneIntegerLattice.indicator, Finset.sum_apply]

/-- Boolean label sum zero is exactly membership in the ORIGINAL integer range. -/
theorem sum_label_zero_iff (S : Finset P) :
    (∑ x ∈ S, label (L := L) x) = 0 ↔
      ProjectivePlaneIntegerLattice.indicator S ∈ ProjectivePlaneIntegerLattice.lattice (L := L) := by
  change (∑ x ∈ S, (QuotientAddGroup.mk' (integerImage (P := P) (L := L)))
    (ProjectivePlaneIntegerLattice.unit x)) = 0 ↔ _
  rw [← map_sum, unit_sum]
  exact QuotientAddGroup.eq_zero_iff _

/-- ALL nonempty proper zero supports in the universal quotient are original lines. -/
theorem universal_zero_support_iff_line (S : Finset P) (hne : S.Nonempty) (hp : S ≠ univ) :
    (∑ x ∈ S, label (L := L) x) = 0 ↔ ∃ l : L, S = lineSupport l := by
  exact (sum_label_zero_iff S).trans
    (ProjectivePlaneIntegerLattice.boolean_mem_lattice_iff S hne hp)

private theorem label_ne_zero (x : P) : label (L := L) x ≠ 0 := by
  intro hz
  have hu : ProjectivePlaneIntegerLattice.unit x ∈
      ProjectivePlaneIntegerLattice.lattice (L := L) :=
    (QuotientAddGroup.eq_zero_iff _).mp hz
  have hd := (ProjectivePlaneIntegerLattice.unit_mem_lattice_iff (L := L) x 1).mp (by simpa using hu)
  change ((q (P := P) (L := L) : ℤ) * ((q (P := P) (L := L) : ℤ)+1)) ∣ 1 at hd
  have hn : q (P := P) (L := L) * (q (P := P) (L := L)+1) ∣ 1 := by exact_mod_cast hd
  have he := Nat.dvd_one.mp hn
  have hq := ProjectivePlane.one_lt_order P L
  change 1 < q (P := P) (L := L) at hq
  nlinarith

private theorem label_injective : Function.Injective (label (P := P) (L := L)) := by
  intro x y he
  by_contra hxy
  have hz : (QuotientAddGroup.mk' (integerImage (P := P) (L := L)))
      (ProjectivePlaneIntegerLattice.unit x - ProjectivePlaneIntegerLattice.unit y) = 0 := by
    rw [map_sub]
    exact sub_eq_zero.mpr he
  have hu : (fun z => ProjectivePlaneIntegerLattice.unit x z - ProjectivePlaneIntegerLattice.unit y z) ∈
      ProjectivePlaneIntegerLattice.lattice (L := L) := (QuotientAddGroup.eq_zero_iff _).mp hz
  have hd := (ProjectivePlaneIntegerLattice.difference_mem_lattice_iff (L := L) x y hxy 1).mp
    (by simpa using hu)
  change (q (P := P) (L := L) : ℤ) ∣ 1 at hd
  have hn : q (P := P) (L := L) ∣ 1 := by exact_mod_cast hd
  have hq := ProjectivePlane.one_lt_order P L
  change 1 < q (P := P) (L := L) at hq
  have := Nat.dvd_one.mp hn
  omega

private theorem universal_total_ne_zero : (∑ x : P, label (L := L) x) ≠ 0 := by
  intro hz
  have hu := (sum_label_zero_iff (L := L) (univ : Finset P)).mp hz
  have hid : ProjectivePlaneIntegerLattice.indicator (univ : Finset P) =
      (fun _ : P => (1 : ℤ)) := by
    funext x
    simp [ProjectivePlaneIntegerLattice.indicator]
  rw [hid] at hu
  have hd := (ProjectivePlaneIntegerLattice.constant_mem_lattice_iff (P := P) (L := L) 1).mp hu
  change (q (P := P) (L := L) : ℤ)+1 ∣ 1 at hd
  have hn : q (P := P) (L := L)+1 ∣ 1 := by exact_mod_cast hd
  have hq := ProjectivePlane.one_lt_order P L
  change 1 < q (P := P) (L := L) at hq
  have := Nat.dvd_one.mp hn
  omega

/-- The exact original quotient has distinct nonzero original unit labels,
nonzero full total, and a literal Good word containing every original point once. -/
theorem universal_good :
    Function.Injective (label (P := P) (L := L)) ∧
    (∀ x : P, label (L := L) x ≠ 0) ∧ (∑ x : P, label (L := L) x) ≠ 0 ∧
    ∃ w : List P, w.Perm (univ : Finset P).toList ∧ Good (w.map (label (L := L))) ∧
      (w.map (label (L := L))).Nodup := by
  obtain ⟨w, hw, ha⟩ := exists_line_avoiding_order (P := P) (L := L)
  refine ⟨label_injective, label_ne_zero, universal_total_ne_zero, w, mem_orders.mp hw, ?_, ?_⟩
  · exact good_map_of_avoiding univ (label (L := L)) (lineSupport (P := P) (L := L))
      (fun S _ hne hp hz => (universal_zero_support_iff_line S hne hp).mp hz)
      (mem_orders.mp hw) ha
  · exact ((mem_orders.mp hw).nodup_iff.mpr univ.nodup_toList).map label_injective

end D5.S3.Geometry.FiniteGeometry.ProjectivePlaneGoodOrdering
