/- GID: D5/S3/Observer/Completion/MonotheticCompactMonoid
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/MonotheticCompactMonoid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The tail of a compact monothetic additive monoid is its minimal ideal group. -/

import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.DenseEmbedding
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Data.ENat.Basic

open Set Topology

namespace D5.S3.Observer.Completion.MonotheticCompactMonoid

variable {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
  [ContinuousAdd M] [CompactSpace M] [T2Space M]

def tail (a : M) (N : ℕ) : Set M :=
  closure (range fun n : ℕ => (N + n) • a)

def core (a : M) : Set M := ⋂ N : ℕ, tail a N

private theorem tail_eq_range (a : M) (hd : DenseRange fun n : ℕ => n • a) (N : ℕ) :
    tail a N = range (fun x : M => N • a + x) := by
  have hc : Continuous (fun x : M => N • a + x) := continuous_const.add continuous_id
  have h := hc.isClosedMap.closure_image_eq_of_continuous hc
    (range fun n : ℕ => n • a)
  rw [hd.closure_range, image_univ, ← Set.range_comp] at h
  simpa only [tail, Function.comp_def, add_nsmul] using h

omit [ContinuousAdd M] [CompactSpace M] [T2Space M] in
private theorem tail_succ_subset (a : M) (N : ℕ) : tail a (N + 1) ⊆ tail a N := by
  apply closure_mono
  rintro _ ⟨n, rfl⟩
  exact ⟨n + 1, by dsimp; congr 1; omega⟩

omit [ContinuousAdd M] [T2Space M] in
private theorem core_nonempty (a : M) : (core a).Nonempty := by
  apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (tail a) (tail_succ_subset a)
  · intro N
    exact ⟨N • a, subset_closure ⟨0, by simp⟩⟩
  · exact isClosed_closure.isCompact
  · intro N; exact isClosed_closure

omit [ContinuousAdd M] [CompactSpace M] [T2Space M] in
private theorem core_closed (a : M) : IsClosed (core a) :=
  isClosed_iInter fun _ => isClosed_closure

private theorem add_mem_core (a : M) (hd : DenseRange fun n : ℕ => n • a)
    (x : M) {y : M} (hy : y ∈ core a) : x + y ∈ core a := by
  apply mem_iInter.mpr
  intro N
  have hyN := mem_iInter.mp hy N
  rw [tail_eq_range a hd N] at hyN ⊢
  obtain ⟨z, rfl⟩ := hyN
  exact ⟨x + z, by dsimp; ac_rfl⟩

private theorem tail_succ_eq_image (a : M) (hd : DenseRange fun n : ℕ => n • a) (N : ℕ) :
    tail a (N + 1) = (fun y => a + y) '' tail a N := by
  rw [tail_eq_range a hd (N + 1), tail_eq_range a hd N, ← Set.range_comp]
  congr 1
  funext x
  simp only [Function.comp_def, add_nsmul, one_nsmul]
  ac_rfl

private theorem generator_surjective_on_core (a : M) (hd : DenseRange fun n : ℕ => n • a)
    {y : M} (hy : y ∈ core a) : ∃ z ∈ core a, a + z = y := by
  let F : ℕ → Set M := fun N => tail a N ∩ {z | a + z = y}
  have hFclosed (N : ℕ) : IsClosed (F N) :=
    isClosed_closure.inter (isClosed_eq (continuous_const.add continuous_id) continuous_const)
  have hFne (N : ℕ) : (F N).Nonempty := by
    have hN := mem_iInter.mp hy (N + 1)
    rw [tail_succ_eq_image a hd N] at hN
    obtain ⟨z, hz, he⟩ := hN
    exact ⟨z, hz, he⟩
  have hFmono (N : ℕ) : F (N + 1) ⊆ F N :=
    inter_subset_inter_left _ (tail_succ_subset a N)
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    F hFmono hFne (hFclosed 0).isCompact hFclosed
  refine ⟨z, mem_iInter.mpr (fun N => (mem_iInter.mp hz N).1), ?_⟩
  exact (mem_iInter.mp hz 0).2

private theorem natural_surjective_on_core (a : M) (hd : DenseRange fun n : ℕ => n • a)
    (n : ℕ) {y : M} (hy : y ∈ core a) : ∃ z ∈ core a, n • a + z = y := by
  induction n generalizing y with
  | zero => exact ⟨y, hy, by simp⟩
  | succ n ih =>
    obtain ⟨w, hw, he⟩ := generator_surjective_on_core a hd hy
    obtain ⟨z, hz, hz'⟩ := ih hw
    refine ⟨z, hz, ?_⟩
    rw [succ_nsmul', add_assoc, hz', he]

private theorem translation_surjective_on_core (a : M) (hd : DenseRange fun n : ℕ => n • a)
    (x : M) {y : M} (hy : y ∈ core a) : ∃ z ∈ core a, x + z = y := by
  let F : Set (M × M) := {p | p.2 ∈ core a ∧ p.1 + p.2 = y}
  have hF : IsClosed F := (core_closed a).preimage continuous_snd |>.inter
    (isClosed_eq (continuous_fst.add continuous_snd) continuous_const)
  have hproj : IsClosed (Prod.fst '' F) := isClosedMap_fst_of_compactSpace F hF
  have hnat (n : ℕ) : n • a ∈ Prod.fst '' F := by
    obtain ⟨z, hz, he⟩ := natural_surjective_on_core a hd n hy
    exact ⟨(n • a, z), ⟨hz, he⟩, rfl⟩
  have hx : x ∈ Prod.fst '' F := hd.induction_on x hproj hnat
  obtain ⟨⟨_, z⟩, ⟨hz, he⟩, rfl⟩ := hx
  exact ⟨z, hz, he⟩

private theorem translation_image_core (a : M) (hd : DenseRange fun n : ℕ => n • a) (x : M) :
    (fun z => x + z) '' core a = core a := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact add_mem_core a hd x hz
  · intro y hy
    exact translation_surjective_on_core a hd x hy

private theorem core_has_identity (a : M) (hd : DenseRange fun n : ℕ => n • a) :
    ∃ e ∈ core a, ∀ z ∈ core a, e + z = z := by
  obtain ⟨b, hb⟩ := core_nonempty a
  obtain ⟨e, he, hbe⟩ := translation_surjective_on_core a hd b hb
  refine ⟨e, he, ?_⟩
  intro z hz
  obtain ⟨c, hc, hbc⟩ := translation_surjective_on_core a hd b hz
  calc
    e + z = e + (b + c) := congrArg (e + ·) hbc.symm
    _ = (b + e) + c := by ac_rfl
    _ = z := by rw [hbe, hbc]

/-- The internal group has the inherited addition, a continuous inverse, and a dense
orbit of the image of the original generator under an additive retraction. -/
theorem core_group_retraction (a : M) (hd : DenseRange fun n : ℕ => n • a) :
    ∃ group : AddCommGroup (core a),
      let := group
      (∀ x y : core a, ((x + y : core a) : M) = (x : M) + (y : M)) ∧
      IsTopologicalAddGroup (core a) ∧
      ∃ r : M →+ core a, Continuous r ∧
        (∀ x : M, (r x : M) = x + ((0 : core a) : M)) ∧
        (∀ x : core a, r (x : M) = x) ∧
        DenseRange (fun n : ℕ => n • r a) := by
  classical
  obtain ⟨e, he, hid⟩ := core_has_identity a hd
  let H := core a
  let : Add H := ⟨fun x y => ⟨x.1 + y.1, add_mem_core a hd x.1 y.2⟩⟩
  let : Zero H := ⟨⟨e, he⟩⟩
  have hinv (x : H) : ∃ y : H, y + x = 0 := by
    obtain ⟨y, hy, hxy⟩ := translation_surjective_on_core a hd x.1 he
    exact ⟨⟨y, hy⟩, Subtype.ext (by change y + x.1 = e; rw [add_comm, hxy])⟩
  let : Neg H := ⟨fun x => Classical.choose (hinv x)⟩
  let : AddCommGroup H :=
    { AddGroup.ofLeftAxioms
        (fun x y z => Subtype.ext (add_assoc x.1 y.1 z.1))
        (fun x => Subtype.ext (hid x.1 x.2))
        (fun x => Classical.choose_spec (hinv x)) with
      add_comm := fun x y => Subtype.ext (add_comm x.1 y.1) }
  have : CompactSpace H := isCompact_iff_compactSpace.mp (core_closed a).isCompact
  have : ContinuousAdd H := ⟨
    ((continuous_subtype_val.comp continuous_fst).add
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _⟩
  have hneg : Continuous (fun x : H => -x) := by
    apply continuous_iff_isClosed.mpr
    intro s hs
    let F : Set (H × H) := {p | p.1 + p.2 = 0 ∧ p.2 ∈ s}
    have hF : IsClosed F :=
      (isClosed_eq (continuous_fst.add continuous_snd) continuous_const).inter
        (hs.preimage continuous_snd)
    have heq : (fun x : H => -x) ⁻¹' s = Prod.fst '' F := by
      ext x
      constructor
      · intro hx
        exact ⟨(x, -x), ⟨add_neg_cancel x, hx⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hxy, hy⟩, rfl⟩
        have hyx : y = -x := by
          calc y = -x + (x + y) := by simp
               _ = -x := by rw [hxy, add_zero]
        change -x ∈ s
        simpa only [hyx] using hy
    rw [heq]
    exact isClosedMap_fst_of_compactSpace F hF
  have : IsTopologicalAddGroup H := { continuous_neg := hneg }
  let r : M →+ H :=
    { toFun := fun x => ⟨x + e, add_mem_core a hd x he⟩
      map_zero' := Subtype.ext (zero_add e)
      map_add' := fun x y => Subtype.ext (by
        change x + y + e = (x + e) + (y + e)
        calc x + y + e = x + y + (e + e) := by rw [hid e he]
             _ = (x + e) + (y + e) := by ac_rfl) }
  have hr : Continuous r := (continuous_id.add continuous_const).subtype_mk _
  have hfix (x : H) : r x = x := Subtype.ext (by
    change x.1 + e = x.1
    rw [add_comm, hid x.1 x.2])
  have hsurj : Function.Surjective r := fun x => ⟨x.1, hfix x⟩
  refine ⟨inferInstance, (fun _ _ => rfl), inferInstance, r, hr,
    (fun _ => rfl), hfix, ?_⟩
  have hd' := hsurj.denseRange.comp hd hr
  simpa only [Function.comp_def, map_nsmul] using hd'

#print axioms core_group_retraction

private theorem prefix_or_tail (a : M) (hd : DenseRange fun n : ℕ => n • a)
    (N : ℕ) (x : M) :
    x ∈ (fun n : ℕ => n • a) '' Iio N ∪ tail a N := by
  apply hd.induction_on (p := fun x => x ∈ (fun n : ℕ => n • a) '' Iio N ∪ tail a N) x
  · exact ((finite_Iio N).image _).isClosed.union isClosed_closure
  · intro n
    by_cases hn : n < N
    · exact Or.inl ⟨n, hn, rfl⟩
    · right
      exact subset_closure ⟨n - N, by dsimp; congr 1; omega⟩

private theorem outside_isolated_orbit (a : M) (hd : DenseRange fun n : ℕ => n • a)
    {x : M} (hx : x ∉ core a) :
    (∃ n : ℕ, x = n • a) ∧ IsOpen ({x} : Set M) := by
  classical
  simp only [core, mem_iInter] at hx
  push Not at hx
  obtain ⟨N, hN⟩ := hx
  let P : Set M := (fun n : ℕ => n • a) '' Iio N
  have hP : P.Finite := (finite_Iio N).image _
  have hxP : x ∈ P := (prefix_or_tail a hd N x).resolve_right hN
  refine ⟨?_, ?_⟩
  · obtain ⟨n, _, hn⟩ := hxP
    exact ⟨n, hn.symm⟩
  · have heq : ({x} : Set M) = (tail a N ∪ (P \ {x}))ᶜ := by
      ext y
      simp only [mem_singleton_iff, mem_compl_iff, mem_union, mem_sdiff,
        not_or, not_and, not_not]
      constructor
      · rintro rfl
        exact ⟨hN, fun _ => rfl⟩
      · rintro ⟨hyN, hy⟩
        exact hy ((prefix_or_tail a hd N y).resolve_right hyN)
    rw [heq]
    exact (isClosed_closure.union hP.sdiff.isClosed).isOpen_compl

private theorem collision_mem_core (a : M) {n m : ℕ}
    (hnm : n < m) (heq : n • a = m • a) : n • a ∈ core a := by
  let p := m - n
  have hp : 0 < p := Nat.sub_pos_of_lt hnm
  have hstep : (n + p) • a = n • a := by
    rw [show n + p = m by omega]
    exact heq.symm
  have hrep (k : ℕ) : (n + k * p) • a = n • a := by
    induction k with
    | zero => simp
    | succ k ih =>
      calc
        (n + (k + 1) * p) • a = ((n + k * p) + p) • a := by congr 1; ring
        _ = (n + k * p) • a + p • a := add_nsmul _ _ _
        _ = (n + p) • a := by rw [ih, add_nsmul]
        _ = n • a := hstep
  apply mem_iInter.mpr
  intro N
  rw [← hrep N]
  apply subset_closure
  have hlarge : N ≤ n + N * p := by
    have := Nat.le_mul_of_pos_right N hp
    omega
  exact ⟨n + N * p - N, by dsimp; congr 1; omega⟩

private theorem core_nsmul_upward (a : M) (hd : DenseRange fun n : ℕ => n • a)
    {n m : ℕ} (hn : n • a ∈ core a) (hnm : n ≤ m) : m • a ∈ core a := by
  have := add_mem_core a hd ((m - n) • a) hn
  rwa [← add_nsmul, Nat.sub_add_cancel hnm] at this

private theorem core_threshold (a : M) (hd : DenseRange fun n : ℕ => n • a) :
    ∃! t : ℕ∞, ∀ n : ℕ, n • a ∉ core a ↔ (n : ℕ∞) < t := by
  classical
  have hex : ∃ t : ℕ∞, ∀ n : ℕ, n • a ∉ core a ↔ (n : ℕ∞) < t := by
    by_cases h : ∃ n : ℕ, n • a ∈ core a
    · refine ⟨(Nat.find h : ℕ∞), ?_⟩
      intro n
      rw [ENat.natCast_lt_natCast]
      constructor
      · intro hn
        by_contra hlt
        exact hn (core_nsmul_upward a hd (Nat.find_spec h) (by omega))
      · exact Nat.find_min h
    · refine ⟨⊤, ?_⟩
      intro n
      simp only [ENat.natCast_lt_top, iff_true]
      exact fun hn => h ⟨n, hn⟩
  obtain ⟨t, ht⟩ := hex
  refine ⟨t, ht, ?_⟩
  intro u hu
  apply eq_of_forall_lt_iff
  intro k
  induction k using ENat.recTopCoe with
  | top => simp
  | coe n => exact (hu n).symm.trans (ht n)

/-- The tail is the least nonempty additive ideal. Its complement is a uniquely
indexed finite or infinite initial segment of isolated, pairwise distinct orbit points. -/
theorem core_ideal_and_threshold (a : M) (hd : DenseRange fun n : ℕ => n • a) :
    (core a).Nonempty ∧ IsCompact (core a) ∧
    (∀ x : M, (fun z => x + z) '' core a = core a) ∧
    (∀ I : Set M, I.Nonempty → (∀ x : M, ∀ y ∈ I, x + y ∈ I) → core a ⊆ I) ∧
    (0 ∈ core a ↔ core a = univ) ∧
    ∃! t : ℕ∞,
      (∀ n : ℕ, n • a ∉ core a ↔ (n : ℕ∞) < t) ∧
      (core a)ᶜ = (fun n : ℕ => n • a) '' {n | (n : ℕ∞) < t} ∧
      Set.InjOn (fun n : ℕ => n • a) {n | (n : ℕ∞) < t} ∧
      (∀ n : ℕ, (n : ℕ∞) < t → IsOpen ({n • a} : Set M)) := by
  refine ⟨core_nonempty a, (core_closed a).isCompact,
    translation_image_core a hd, ?_, ?_, ?_⟩
  · intro I hI hideal z hz
    obtain ⟨x, hx⟩ := hI
    obtain ⟨y, hy, hxy⟩ := translation_surjective_on_core a hd x hz
    rw [← hxy, add_comm]
    exact hideal y x hx
  · constructor
    · intro hzero
      apply eq_univ_of_forall
      intro x
      simpa only [add_zero] using add_mem_core a hd x hzero
    · intro h
      rw [h]
      trivial
  · obtain ⟨t, ht, huniq⟩ := core_threshold a hd
    refine ⟨t, ⟨ht, ?_, ?_, ?_⟩, fun u hu => huniq u hu.1⟩
    · ext x
      constructor
      · intro hx
        obtain ⟨n, rfl⟩ := (outside_isolated_orbit a hd hx).1
        exact ⟨n, (ht n).mp hx, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        exact (ht n).mpr hn
    · intro n hn m hm heq
      rcases lt_trichotomy n m with hlt | he | hgt
      · exact ((ht n).mpr hn (collision_mem_core a hlt heq)).elim
      · exact he
      · exact ((ht m).mpr hm (collision_mem_core a hgt heq.symm)).elim
    · intro n hn
      exact (outside_isolated_orbit a hd ((ht n).mpr hn)).2

#print axioms core_ideal_and_threshold

end D5.S3.Observer.Completion.MonotheticCompactMonoid
