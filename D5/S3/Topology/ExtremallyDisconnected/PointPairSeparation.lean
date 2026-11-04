/- GID: D5/S3/Topology/ExtremallyDisconnected/PointPairSeparation
   generality: G
   mirror-B: D5/B/S3/Topology/ExtremallyDisconnected/PointPairSeparation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Eventual agreement on every clopen forces eventual equality of point pairs. -/

import Mathlib.Topology.ExtremallyDisconnected
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Set.Finite.Powerset

/-!
# Eventual equality from clopen membership tests

The shell construction applies to arbitrary Hausdorff extremally disconnected spaces.
-/

open Set Filter Topology

namespace D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation

universe u

theorem enumerate_pool {A : Set ℕ} (hA : A.Infinite) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∀ n, a n ∈ A := by
  exact Nat.exists_strictMono_subsequence (fun N => by
    obtain ⟨n, hn, hN⟩ := hA.exists_gt N
    exact ⟨n, hN, hn⟩)

theorem split_pool {A : Set ℕ} (hA : A.Infinite) :
    ∃ T V : Set ℕ, T ⊆ A ∧ V ⊆ A ∧ T.Infinite ∧ V.Infinite ∧ Disjoint T V := by
  obtain ⟨a, ha, hmem⟩ := enumerate_pool hA
  refine ⟨range (fun n => a (2 * n)), range (fun n => a (2 * n + 1)),
    ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩; exact hmem _
  · rintro _ ⟨n, rfl⟩; exact hmem _
  · apply infinite_range_of_injective
    intro n m h
    have := ha.injective h
    omega
  · apply infinite_range_of_injective
    intro n m h
    have := ha.injective h
    omega
  · apply disjoint_left.mpr
    rintro _ ⟨n, rfl⟩ ⟨m, hm⟩
    have := ha.injective hm
    omega

theorem diagonal_pool (A : ℕ → Set ℕ) (hA : ∀ n, (A n).Infinite)
    (hdec : ∀ n, A (n + 1) ⊆ A n) :
    ∃ S : Set ℕ, S.Infinite ∧ S ⊆ A 0 ∧ ∀ n, (S \ A n).Finite := by
  classical
  have hchoose : ∀ n m : ℕ, ∃ k ∈ A n, m < k := fun n m => (hA n).exists_gt m
  choose f hfmem hfgt using hchoose
  let a : ℕ → ℕ := fun n => Nat.rec (f 0 0) (fun n prev => f (n + 1) prev) n
  have ha : ∀ n, a n ∈ A n := by
    intro n; cases n with
    | zero => exact hfmem 0 0
    | succ n => exact hfmem (n + 1) (a n)
  have hmono : StrictMono a := strictMono_nat_of_lt_succ (fun n => hfgt (n + 1) (a n))
  have hanti : Antitone A := antitone_nat_of_succ_le hdec
  refine ⟨range a, infinite_range_of_injective hmono.injective, ?_, ?_⟩
  · rintro _ ⟨n, rfl⟩
    exact hanti (Nat.zero_le n) (ha n)
  · intro m
    apply (Set.finite_Iio m).image a |>.subset
    rintro _ ⟨⟨n, rfl⟩, hn⟩
    refine ⟨n, ?_, rfl⟩
    change n < m
    by_contra h
    exact hn (hanti (by omega : m ≤ n) (ha n))

variable {E : Type u} [TopologicalSpace E]

private def shellOpen (D : ℕ → Set E) (A : Set ℕ) : Set E := ⋃ i ∈ A, D i

private theorem shellOpen_open {D : ℕ → Set E} (hD : ∀ i, IsClopen (D i))
    (A : Set ℕ) : IsOpen (shellOpen D A) :=
  isOpen_iUnion (fun i => isOpen_iUnion (fun _ => (hD i).isOpen))

private theorem shell_closures_disjoint [ExtremallyDisconnected E]
    {D : ℕ → Set E} (hD : ∀ i, IsClopen (D i))
    (hdis : Pairwise (fun i j => Disjoint (D i) (D j)))
    {A B : Set ℕ} (hAB : Disjoint A B) :
    Disjoint (closure (shellOpen D A)) (closure (shellOpen D B)) := by
  apply ExtremallyDisconnected.disjoint_closure_of_disjoint_isOpen
    (hU₁ := shellOpen_open hD A) (hU₂ := shellOpen_open hD B)
  apply disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
  obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hy
  by_cases hij : i = j
  · exact (disjoint_left.mp hAB hi (hij ▸ hj))
  · exact disjoint_left.mp (hdis hij) hxi hxj

private theorem closure_finite_error {D : ℕ → Set E} (hD : ∀ i, IsClopen (D i))
    {S A : Set ℕ} (hfin : (S \ A).Finite) :
    closure (shellOpen D S) ⊆ closure (shellOpen D A) ∪ shellOpen D (S \ A) := by
  apply closure_minimal
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    by_cases hiA : i ∈ A
    · exact Or.inl (subset_closure (mem_iUnion₂.mpr ⟨i, hiA, hxi⟩))
    · exact Or.inr (mem_iUnion₂.mpr ⟨i, ⟨hi, hiA⟩, hxi⟩)
  · exact isClosed_closure.union (hfin.isClosed_biUnion (fun i _ => (hD i).isClosed))

omit [TopologicalSpace E] in
private theorem sparse_avoidance {D : ℕ → Set E} {y : ℕ → E}
    (hdis : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hforward : ∀ i j, y i ∈ D j → i < j) :
    ∃ b : ℕ → ℕ, StrictMono b ∧ ∀ n m, y (b n) ∉ D (b m) := by
  classical
  let r : ℕ → ℕ := fun i => if h : ∃ j, y i ∈ D j then h.choose else i
  have hr : ∀ i j, y i ∈ D j → j = r i := by
    intro i j hj
    have h : ∃ j, y i ∈ D j := ⟨j, hj⟩
    have hri : y i ∈ D (r i) := by simpa [r, h] using h.choose_spec
    by_contra hne
    exact disjoint_left.mp (hdis hne) hj hri
  let b : ℕ → ℕ := fun n => Nat.rec 0 (fun _ v => max v (r v) + 1) n
  have hb : ∀ n, b (n + 1) = max (b n) (r (b n)) + 1 := fun _ => rfl
  have hmono : StrictMono b := strictMono_nat_of_lt_succ (fun n => by
    rw [hb]; exact lt_of_le_of_lt (le_max_left _ _) (Nat.lt_succ_self _))
  refine ⟨b, hmono, ?_⟩
  intro n m hm
  have heq := hr (b n) (b m) hm
  have hlt := hforward (b n) (b m) hm
  by_cases hmn : m ≤ n
  · have := hmono.monotone hmn
    omega
  · have hm' : n + 1 ≤ m := by omega
    have := hmono.monotone hm'
    have hskip : r (b n) < b (n + 1) := by rw [hb]; omega
    omega

private theorem separate_shells [ExtremallyDisconnected E]
    {D : ℕ → Set E} {x y : ℕ → E}
    (hD : ∀ i, IsClopen (D i))
    (hdis : Pairwise (fun i j => Disjoint (D i) (D j)))
    (hx : ∀ i, x i ∈ D i) (hforward : ∀ i j, y i ∈ D j → i < j) :
    ∃ U : Set E, IsClopen U ∧ {i | x i ∈ U ∧ y i ∉ U}.Infinite := by
  classical
  obtain ⟨b, hb, havoid⟩ := sparse_avoidance hdis hforward
  let B := range b
  have hB : B.Infinite := infinite_range_of_injective hb.injective
  let Q : Set ℕ → Set E := fun A => closure (shellOpen D A)
  have half : ∀ A : Set ℕ, A.Infinite → ∀ z : E,
      ∃ A' : Set ℕ, A' ⊆ A ∧ A'.Infinite ∧ z ∉ Q A' := by
    intro A hA z
    obtain ⟨T, V, hTA, hVA, hT, hV, hTV⟩ := split_pool hA
    have hd := shell_closures_disjoint hD hdis hTV
    by_cases hz : z ∈ Q T
    · exact ⟨V, hVA, hV, fun hzV => disjoint_left.mp hd hz hzV⟩
    · exact ⟨T, hTA, hT, hz⟩
  let next : (ℕ × {A : Set ℕ // A.Infinite}) → {A : Set ℕ // A.Infinite} := fun w =>
    ⟨(half w.2.val w.2.property (y (b w.1))).choose,
      (half w.2.val w.2.property (y (b w.1))).choose_spec.2.1⟩
  let pools : ℕ → {A : Set ℕ // A.Infinite} :=
    fun n => Nat.rec ⟨B, hB⟩ (fun n A => next (n, A)) n
  let A : ℕ → Set ℕ := fun n => (pools n).val
  have hdec : ∀ n, A (n + 1) ⊆ A n := fun n =>
    (half (A n) (pools n).property (y (b n))).choose_spec.1
  have hmiss : ∀ n, y (b n) ∉ Q (A (n + 1)) := fun n =>
    (half (A n) (pools n).property (y (b n))).choose_spec.2.2
  obtain ⟨S, hS, hSB, hfin⟩ := diagonal_pool A (fun n => (pools n).property) hdec
  have hSB' : S ⊆ B := hSB
  have hmissS : ∀ n, y (b n) ∉ Q S := by
    intro n hyn
    have hc := closure_finite_error hD (hfin (n + 1)) hyn
    rcases hc with hc | hc
    · exact hmiss n hc
    · obtain ⟨j, hj, hyj⟩ := mem_iUnion₂.mp hc
      obtain ⟨m, rfl⟩ := hSB' hj.1
      exact havoid n m hyj
  refine ⟨Q S, ⟨isClosed_closure, ExtremallyDisconnected.open_closure _ (shellOpen_open hD S)⟩,
    hS.mono ?_⟩
  intro i hi
  refine ⟨subset_closure (mem_iUnion₂.mpr ⟨i, hi, hx i⟩), ?_⟩
  obtain ⟨n, rfl⟩ := hSB' hi
  exact hmissS n

private structure Pool (p q : ℕ → E) where
  C : Set E
  clopen : IsClopen C
  L : Set ℕ
  infinite : L.Infinite
  within : ∀ m ∈ L, p m ∈ C ∧ q m ∈ C
  unequal : ∀ m ∈ L, p m ≠ q m

private structure PoolStep {p q : ℕ → E} (s : Pool p q) where
  next : Pool p q
  k : ℕ
  kmem : k ∈ s.L
  shrink : next.C ⊆ s.C
  later : ∀ m ∈ next.L, k < m
  x : E
  y : E
  orientation : (x = p k ∧ y = q k) ∨ (x = q k ∧ y = p k)
  discarded : x ∈ s.C \ next.C
  retained : y ∈ next.C

private theorem pool_step_exists [T2Space E] [ExtremallyDisconnected E]
    {p q : ℕ → E}
    (hagree : ∀ U : Set E, IsClopen U → ∀ᶠ n in atTop, (p n ∈ U ↔ q n ∈ U))
    (s : Pool p q) : Nonempty (PoolStep s) := by
  classical
  obtain ⟨k, hk⟩ := s.infinite.nonempty
  obtain ⟨H₀, hH₀, hpH₀, hqH₀⟩ := exists_isClopen_of_totally_separated (s.unequal k hk)
  let H := s.C ∩ H₀
  have hH : IsClopen H := s.clopen.inter hH₀
  have hpH : p k ∈ H := ⟨(s.within k hk).1, hpH₀⟩
  have hqH : q k ∉ H := fun h => hqH₀ h.2
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hagree H hH)
  let tail := s.L \ Iio (max N (k + 1))
  have htail : tail.Infinite := s.infinite.sdiff (finite_Iio _)
  have htailL : tail ⊆ s.L := fun _ h => h.1
  have htailN : ∀ m ∈ tail, N ≤ m := by
    intro m hm; have : ¬ m < max N (k + 1) := hm.2; omega
  have htailk : ∀ m ∈ tail, k < m := by
    intro m hm; have : ¬ m < max N (k + 1) := hm.2; omega
  let T := {m ∈ tail | p m ∈ H}
  by_cases hT : T.Infinite
  · let next : Pool p q := {
      C := H
      clopen := hH
      L := T
      infinite := hT
      within := fun m hm => ⟨hm.2, (hN m (htailN m hm.1)).mp hm.2⟩
      unequal := fun m hm => s.unequal m (htailL hm.1) }
    exact ⟨{
      next := next
      k := k
      kmem := hk
      shrink := inter_subset_left
      later := fun m hm => htailk m hm.1
      x := q k
      y := p k
      orientation := Or.inr ⟨rfl, rfl⟩
      discarded := ⟨(s.within k hk).2, hqH⟩
      retained := hpH }⟩
  · have hV : (tail \ T).Infinite := htail.sdiff (Set.not_infinite.mp hT)
    have hnot : ∀ m ∈ tail \ T, p m ∉ H ∧ q m ∉ H := by
      intro m hm
      have hp : p m ∉ H := fun hp => hm.2 ⟨hm.1, hp⟩
      exact ⟨hp, fun hq => hp ((hN m (htailN m hm.1)).mpr hq)⟩
    let next : Pool p q := {
      C := s.C \ H
      clopen := s.clopen.diff hH
      L := tail \ T
      infinite := hV
      within := fun m hm => ⟨⟨(s.within m (htailL hm.1)).1, (hnot m hm).1⟩,
        ⟨(s.within m (htailL hm.1)).2, (hnot m hm).2⟩⟩
      unequal := fun m hm => s.unequal m (htailL hm.1) }
    exact ⟨{
      next := next
      k := k
      kmem := hk
      shrink := sdiff_subset
      later := fun m hm => htailk m hm.1
      x := p k
      y := q k
      orientation := Or.inl ⟨rfl, rfl⟩
      discarded := ⟨(s.within k hk).1, fun h => h.2 hpH⟩
      retained := ⟨(s.within k hk).2, hqH⟩ }⟩

/-- On an arbitrary Hausdorff extremally disconnected space, agreement of each
fixed clopen membership test eventually implies eventual equality. The cutoff
may depend on the clopen, and no compactness is assumed. -/
theorem eventually_eq_of_eventually_mem_isClopen_iff [T2Space E] [ExtremallyDisconnected E]
    (p q : ℕ → E)
    (hagree : ∀ U : Set E, IsClopen U → ∀ᶠ n in atTop, (p n ∈ U ↔ q n ∈ U)) :
    ∀ᶠ n in atTop, p n = q n := by
  classical
  by_contra heq
  have hI : {n | p n ≠ q n}.Infinite := by
    apply Set.infinite_of_forall_exists_gt
    intro N
    have h : ∃ n, N + 1 ≤ n ∧ p n ≠ q n := by
      by_contra hn
      apply heq
      apply eventually_atTop.mpr
      refine ⟨N + 1, ?_⟩
      intro n hn'
      by_contra hne
      exact hn ⟨n, hn', hne⟩
    obtain ⟨n, hn, hne⟩ := h
    exact ⟨n, hne, by omega⟩
  let init : Pool p q := {
    C := univ, clopen := isClopen_univ,
    L := {n | p n ≠ q n}, infinite := hI,
    within := fun _ _ => ⟨mem_univ _, mem_univ _⟩,
    unequal := fun _ h => h }
  let step : (s : Pool p q) → PoolStep s := fun s => (pool_step_exists hagree s).some
  let states : ℕ → Pool p q := fun n => Nat.rec init (fun _ s => (step s).next) n
  let C : ℕ → Set E := fun n => (states n).C
  let k : ℕ → ℕ := fun n => (step (states n)).k
  let x : ℕ → E := fun n => (step (states n)).x
  let y : ℕ → E := fun n => (step (states n)).y
  let D : ℕ → Set E := fun n => C n \ C (n + 1)
  have hC : ∀ n, IsClopen (C n) := fun n => (states n).clopen
  have hdec : ∀ n, C (n + 1) ⊆ C n := fun n => (step (states n)).shrink
  have hanti : Antitone C := antitone_nat_of_succ_le hdec
  have hk : StrictMono k := strictMono_nat_of_lt_succ (fun n =>
    (step (states n)).later _ (step (states (n + 1))).kmem)
  have hx : ∀ n, x n ∈ D n := fun n => (step (states n)).discarded
  have hy : ∀ n, y n ∈ C (n + 1) := fun n => (step (states n)).retained
  have hD : ∀ n, IsClopen (D n) := fun n => (hC n).diff (hC (n + 1))
  have hdis : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro z hzi hzj
    rcases lt_or_gt_of_ne hij with h | h
    · exact hzi.2 (hanti (by omega : i + 1 ≤ j) hzj.1)
    · exact hzj.2 (hanti (by omega : j + 1 ≤ i) hzi.1)
  have hforward : ∀ i j, y i ∈ D j → i < j := by
    intro i j hj
    by_contra h
    exact hj.2 (hanti (by omega : j + 1 ≤ i + 1) (hy i))
  obtain ⟨U, hU, hinf⟩ := separate_shells hD hdis hx hforward
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hagree U hU)
  obtain ⟨i, hi, hNi⟩ := hinf.exists_gt N
  have hki : N ≤ k i := le_trans (by omega : N ≤ i) (hk.id_le i)
  change x i ∈ U ∧ y i ∉ U at hi
  have htest := hN (k i) hki
  have hor : (x i = p (k i) ∧ y i = q (k i)) ∨
      (x i = q (k i) ∧ y i = p (k i)) := (step (states i)).orientation
  rcases hor with ho | ho
  · rw [ho.1, ho.2] at hi
    exact hi.2 (htest.mp hi.1)
  · rw [ho.1, ho.2] at hi
    exact hi.2 (htest.mpr hi.1)

#print axioms eventually_eq_of_eventually_mem_isClopen_iff

end D5.S3.Topology.ExtremallyDisconnected.PointPairSeparation
