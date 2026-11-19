/- GID: D5/S3/Topology/InverseLimit/TalagrandFiniteFibres
   generality: G
   mirror-B: D5/B/S3/Topology/InverseLimit/TalagrandFiniteFibres
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite-to-one maps on the Talagrand compactum have finitely many multiple fibres. -/

import D5.S3.Topology.InverseLimit.SignedBallHistoryEndpoints
import D5.S3.Topology.InverseLimit.ContinuousFiniteImageTail

/-! Clopen separation of disjoint columns, a uniform fibre bound, and finiteness
of the multiple fibres on the actual Talagrand compactum. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Function Filter Topology TopologicalSpace

namespace D5.S3.Topology.InverseLimit.TalagrandFiniteFibres

universe u v w

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [T2Space K]

/-- The sequential weak-star to weak implication for the real dual of `C(K)`. -/
def Grothendieck (K : Type u) [TopologicalSpace K] [CompactSpace K] : Prop :=
  ∀ (F : ℕ → StrongDual ℝ C(K, ℝ)) (L : StrongDual ℝ C(K, ℝ)),
    (∀ g, Tendsto (fun n => F n g) atTop (𝓝 (L g))) →
    ∀ Φ : StrongDual ℝ (StrongDual ℝ C(K, ℝ)),
      Tendsto (fun n => Φ (F n)) atTop (𝓝 (Φ L))

section Separation

variable [ZeroDimensionalSpace K]

private theorem exists_clopen_frequently (hG : Grothendieck K)
    (a b : ℕ → K) (hab : ∀ n m, a n ≠ b m) :
    ∃ U : Set K, IsClopen U ∧ ∃ᶠ n in atTop, a n ∈ U ∧ b n ∉ U := by
  classical
  by_contra hnone
  let F (n : ℕ) : StrongDual ℝ C(K, ℝ) :=
    ContinuousMap.evalCLM (R := ℝ) (a n) - ContinuousMap.evalCLM (R := ℝ) (b n)
  have hF (n : ℕ) (g : C(K, ℝ)) : F n g = g (a n) - g (b n) := rfl
  have hstar (g : C(K, ℝ)) : Tendsto (fun n => F n g) atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_nhds.2
    intro ε hε
    by_contra hbad
    let S : Set (K × K) := {p | ε ≤ dist (g p.1 - g p.2) 0}
    have hS : IsClosed S := isClosed_le continuous_const (by fun_prop)
    have hfreq : ∃ᶠ n in atTop, (a n, b n) ∈ S := by
      simpa only [Filter.Frequently, S, Set.mem_ofPred_eq, not_le, hF] using hbad
    obtain ⟨p, hp, hc⟩ := hS.isCompact.exists_mapClusterPt_of_frequently hfreq
    have hpne : p.1 ≠ p.2 := by
      intro heq
      apply hε.not_ge
      simpa [S, heq] using hp
    obtain ⟨U, hU, hpa, hpb⟩ := exists_isClopen_of_totally_separated hpne
    exact hnone ⟨U, hU, hc.frequently ((hU.isOpen.prod hU.compl.isOpen).mem_nhds
      (show p ∈ U ×ˢ Uᶜ from ⟨hpa, hpb⟩))⟩
  -- Finite clopen tests extend to one bidual test by weak-star compactness.
  let S (n : ℕ) : Set (WeakDual ℝ (StrongDual ℝ C(K, ℝ))) :=
    {Φ | Φ (F n) = 1}
  obtain ⟨Φ, _, hΦ⟩ := (WeakDual.isCompact_closedBall
      (0 : StrongDual ℝ (StrongDual ℝ C(K, ℝ))) 1).inter_iInter_nonempty S
    (fun n => isClosed_eq (WeakDual.eval_continuous (F n)) continuous_const)
    (by
      intro s
      choose U hU ha hb using
        fun i j => exists_isClopen_of_totally_separated (hab i j)
      let V := ⋃ i ∈ s, ⋂ j ∈ s, U i j
      have hV : IsClopen V :=
        isClopen_biUnion_finset fun i _ => isClopen_biInter_finset fun j _ => hU i j
      let g : C(K, ℝ) := ⟨V.indicator (fun _ => 1), hV.continuous_indicator continuous_const⟩
      have hg : ‖g‖ ≤ 1 := (ContinuousMap.norm_le _ zero_le_one).2 fun x => by
        by_cases hx : x ∈ V <;> simp [g, hx]
      let Ψ := NormedSpace.inclusionInDoubleDual ℝ C(K, ℝ) g
      refine ⟨StrongDual.toWeakDual Ψ, ?_, mem_iInter₂.2 fun n hn => ?_⟩
      · change dist Ψ 0 ≤ 1
        rw [dist_zero_right]
        exact (NormedSpace.double_dual_bound ℝ C(K, ℝ) g).trans hg
      · have hav : a n ∈ V :=
          mem_iUnion₂.2 ⟨n, hn, mem_iInter₂.2 fun j _ => ha n j⟩
        have hbv : b n ∉ V := by
          intro hm
          obtain ⟨i, _, hi⟩ := mem_iUnion₂.1 hm
          exact hb i n (mem_iInter₂.1 hi n hn)
        change F n g = 1
        simp [hF, g, hav, hbv])
  have hw := hG F 0 (fun g => by simpa using hstar g) (WeakDual.toStrongDual Φ)
  have hone (n : ℕ) : Φ (F n) = 1 := mem_iInter.1 hΦ n
  have hlim : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
    simpa only [WeakDual.toStrongDual_apply, hone, map_zero] using hw
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hlim)

/-- Disjoint columns with eventually distinct rows admit a single subsequence
on which every ordered pair of rows is eventually separated by a fixed clopen. -/
theorem exists_subseq_pairwise_clopen_separation (hG : Grothendieck K)
    {I : Type w} [Countable I] [Nonempty I] (x : I → ℕ → K)
    (hcols : ∀ i j n m, n ≠ m → x i n ≠ x j m)
    (hrows : ∀ i j, i ≠ j → ∀ᶠ n in atTop, x i n ≠ x j n) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ i j, i ≠ j → ∃ U : Set K, IsClopen U ∧
        ∀ᶠ n in atTop, x i (σ n) ∈ U ∧ x j (σ n) ∉ U := by
  classical
  obtain ⟨pair, hpair⟩ := exists_surjective_nat (I × I)
  have step (p : I × I) (r : ℕ ↪o ℕ) :
      ∃ (t : ℕ ↪o ℕ) (U : Set K), IsClopen U ∧
        (p.1 ≠ p.2 → ∀ n, x p.1 (r (t n)) ∈ U ∧ x p.2 (r (t n)) ∉ U) := by
    by_cases hp : p.1 = p.2
    · exact ⟨OrderEmbedding.ofStrictMono id strictMono_id, univ, isClopen_univ,
        fun h => (h hp).elim⟩
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (r.strictMono.tendsto_atTop.eventually (hrows p.1 p.2 hp))
    obtain ⟨U, hU, hfreq⟩ := exists_clopen_frequently hG
      (fun n => x p.1 (r (N + n))) (fun n => x p.2 (r (N + n))) (by
        intro n m
        by_cases hnm : n = m
        · subst m
          exact hN _ (Nat.le_add_right N n)
        · exact hcols _ _ _ _ (r.injective.ne (by omega)))
    obtain ⟨t, ht, htU⟩ := extraction_of_frequently_atTop hfreq
    have hmono : StrictMono (fun n => N + t n) := fun n m hnm =>
      Nat.add_lt_add_left (ht hnm) N
    exact ⟨OrderEmbedding.ofStrictMono _ hmono, U, hU, fun _ => htU⟩
  choose refineIndex U hU hsep using step
  let r : ℕ → ℕ ↪o ℕ := Nat.rec (OrderEmbedding.ofStrictMono id strictMono_id)
    (fun n r => (refineIndex (pair n) r).trans r)
  have hr (n : ℕ) : r (n + 1) = (refineIndex (pair n) (r n)).trans (r n) := rfl
  have hrApply (n m : ℕ) : r (n + 1) m = r n (refineIndex (pair n) (r n) m) := by
    rw [hr]
    rfl
  have hnest : Antitone (fun n => range (r n)) := by
    apply antitone_nat_of_succ_le
    intro n
    rintro _ ⟨m, rfl⟩
    exact ⟨refineIndex (pair n) (r n) m, (hrApply n m).symm⟩
  refine ⟨fun n => r n n, strictMono_nat_of_lt_succ (fun n => ?_), ?_⟩
  · rw [hrApply]
    apply (r n).strictMono
    exact (Nat.lt_succ_self n).trans_le
      ((refineIndex (pair n) (r n)).strictMono.id_le (n + 1))
  · intro i j hij
    obtain ⟨n, hn⟩ := hpair (i, j)
    refine ⟨U (pair n) (r n), hU _ _, eventually_atTop.2 ⟨n + 1, fun m hm => ?_⟩⟩
    obtain ⟨l, hl⟩ := hnest hm (mem_range_self m)
    change x i (r m m) ∈ _ ∧ x j (r m m) ∉ _
    rw [← hl, hrApply]
    simpa only [hn] using
      hsep (pair n) (r n) (by simpa only [hn] using hij) l

end Separation

variable {Y : Type v} [TopologicalSpace Y] [T2Space Y]

/-- Pointwise finite fibres of a continuous map out of a zero-dimensional
Grothendieck compactum have a uniform cardinal bound. -/
theorem exists_uniform_fibre_bound [ZeroDimensionalSpace K] (hG : Grothendieck K)
    (q : K → Y) (hq : Continuous q) (hfin : ∀ y : Y, (q ⁻¹' {y}).Finite) :
    ∃ M : ℕ, ∀ y : Y, Nat.card (q ⁻¹' {y} : Set K) ≤ M := by
  classical
  by_contra! hunbounded
  let size (y : Y) := Nat.card (q ⁻¹' {y} : Set K)
  choose pick hpick using hunbounded
  let y : ℕ → Y := Nat.rec (pick 0) (fun n y => pick (max (n + 1) (size y)))
  have hstep (n : ℕ) : size (y n) < size (y (n + 1)) :=
    (le_max_right (n + 1) (size (y n))).trans_lt (hpick _)
  have hy : Injective y := by
    intro n m h
    exact (strictMono_nat_of_lt_succ hstep).injective (congrArg size h)
  have hsize (n : ℕ) : n < size (y n) := by
    cases n with
    | zero => exact hpick 0
    | succ n => exact (le_max_left (n + 1) (size (y n))).trans_lt (hpick _)
  let e (n : ℕ) : Fin (size (y n)) ≃ (q ⁻¹' {y n} : Set K) :=
    letI := (hfin (y n)).to_subtype
    (Finite.equivFinOfCardEq rfl).symm
  let x (i n : ℕ) : K :=
    (e n (if h : i < size (y n) then ⟨i, h⟩ else ⟨0, (Nat.zero_le n).trans_lt (hsize n)⟩)).1
  have hx (i n : ℕ) : q (x i n) = y n := (e n _).2
  obtain ⟨σ, hσ, hsep⟩ := exists_subseq_pairwise_clopen_separation hG x
    (fun i j n m hnm h => hnm (hy ((hx i n).symm.trans ((congrArg q h).trans (hx j m)))))
    (by
      intro i j hij
      filter_upwards [eventually_ge_atTop (max i j)] with n hn
      have hi := ((le_max_left i j).trans hn).trans_lt (hsize n)
      have hj := ((le_max_right i j).trans hn).trans_lt (hsize n)
      intro heq
      have h := congrArg Fin.val ((e n).injective (Subtype.ext heq))
      exact hij (by simpa [hi, hj] using h))
  let t (n i : ℕ) := x i (σ n)
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_mapClusterPt
    (f := atTop) (u := t) (by simp)
  have hpq (i : ℕ) : q (p i) = q (p 0) := by
    apply (isClosed_eq (hq.comp (continuous_apply i)) (hq.comp (continuous_apply 0)))
      |>.mem_of_mapClusterPt hp
    exact Eventually.of_forall fun n => (hx i (σ n)).trans (hx 0 (σ n)).symm
  have hinj : Injective p := by
    intro i j hij
    by_contra hne
    obtain ⟨U, hU, he⟩ := hsep i j hne
    have hi : p i ∈ U := (hU.isClosed.preimage (continuous_apply i)).mem_of_mapClusterPt hp
      (he.mono fun _ h => h.1)
    have hclosed : IsClosed {p : ℕ → K | p j ∈ Uᶜ} :=
      hU.compl.isClosed.preimage (continuous_apply j)
    have hj : p j ∈ Uᶜ := hclosed.mem_of_mapClusterPt hp (he.mono fun _ h => h.2)
    exact (show p j ∉ U from hj) (hij ▸ hi)
  exact (hfin (q (p 0))).to_subtype.not_infinite (Infinite.of_injective
    (fun i : ℕ => (⟨p i, hpq i⟩ : (q ⁻¹' {q (p 0)} : Set K)))
    (fun _ _ h => hinj (congrArg Subtype.val h)))

private theorem exists_subseq_tendsto_of_finite_cluster {X : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] (x : ℕ → X)
    (hfin : {p | MapClusterPt p atTop x}.Finite) :
    ∃ (p : X) (σ : ℕ → ℕ), StrictMono σ ∧ Tendsto (x ∘ σ) atTop (𝓝 p) := by
  obtain ⟨p, _, hp⟩ := isCompact_univ.exists_mapClusterPt (f := atTop) (u := x) (by simp)
  have hopen : IsOpen ({p | MapClusterPt p atTop x} \ {p})ᶜ :=
    (hfin.subset sdiff_subset).isClosed.isOpen_compl
  obtain ⟨D, hD, hDc, hDsub⟩ := exists_mem_nhds_isClosed_subset
    (hopen.mem_nhds (show p ∈ ({z | MapClusterPt z atTop x} \ {p})ᶜ by simp))
  obtain ⟨σ, hσ, hmem⟩ := extraction_of_frequently_atTop (hp.frequently hD)
  refine ⟨p, σ, hσ, tendsto_nhds_of_unique_mapClusterPt ?_⟩
  intro z hz
  have hzD := hDc.mem_of_mapClusterPt hz (Eventually.of_forall hmem)
  have hzx := MapClusterPt.of_comp hσ.tendsto_atTop hz
  by_contra hne
  exact hDsub hzD ⟨hzx, hne⟩

private theorem no_injective_limit_of_finite_fibres
    (q : K → Y) (hq : Continuous q) (hfin : ∀ y : Y, (q ⁻¹' {y}).Finite)
    (hseq : ∀ (x : ℕ → K) (p : K), Tendsto x atTop (𝓝 p) →
      ∀ᶠ n in atTop, x n = p)
    (y : ℕ → Y) (hy : Injective y) (hmem : ∀ n, y n ∈ range q) (p : Y) :
    ¬ Tendsto y atTop (𝓝 p) := by
  intro ht
  choose x hx using hmem
  have hfin' : {z | MapClusterPt z atTop x}.Finite := (hfin p).subset (by
    intro z hz
    have hzq := MapClusterPt.continuousAt_comp hq.continuousAt hz
    have hqconv : Tendsto (q ∘ x) atTop (𝓝 p) := by
      rwa [show q ∘ x = y from funext hx]
    change q z = p
    by_contra hne
    exact clusterPt_iff_not_disjoint.1 hzq.clusterPt
      ((disjoint_nhds_nhds.2 hne).mono_right hqconv))
  obtain ⟨z, σ, hσ, hconv⟩ := exists_subseq_tendsto_of_finite_cluster x hfin'
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hseq _ z hconv)
  have he := congrArg q ((hN N le_rfl).trans (hN (N + 1) (Nat.le_succ N)).symm)
  exact (Nat.ne_of_lt (Nat.lt_succ_self N)) (hσ.injective (hy (by simpa [hx] using he)))

private theorem finite_nonsingleton_fibres_of_endpoints [ZeroDimensionalSpace K]
    (hG : Grothendieck K)
    (hseq : ∀ (x : ℕ → K) (p : K), Tendsto x atTop (𝓝 p) →
      ∀ᶠ n in atTop, x n = p)
    (hcopy : ∀ (A B : Set K), IsClosed A → (A ≃ₜ B) → Disjoint A B →
      A.Finite ∧ B.Finite)
    (q : K → Y) (hq : Continuous q) (hfin : ∀ y : Y, (q ⁻¹' {y}).Finite) :
    {y | 1 < Nat.card (q ⁻¹' {y} : Set K)}.Finite := by
  classical
  obtain ⟨M, hM⟩ := exists_uniform_fibre_bound hG q hq hfin
  let size (y : Y) := Nat.card (q ⁻¹' {y} : Set K)
  change {y | 1 < size y}.Finite
  by_contra hinf
  let I := {k ∈ Finset.Icc 2 M | {y | size y = k}.Infinite}
  have hmemI (l : ℕ) (hl : 2 ≤ l) (hi : {y | size y = l}.Infinite) : l ∈ I := by
    obtain ⟨y, hy⟩ := hi.nonempty
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hl, hy ▸ hM y⟩, hi⟩
  have hInonempty : I.Nonempty := by
    by_contra hnone
    apply hinf
    apply ((Finset.Icc 2 M).finite_toSet.biUnion
      (t := fun l => {y | size y = l}) (fun l hl => ?_)).subset
    · intro y hy
      exact mem_iUnion₂.2 ⟨size y, Finset.mem_Icc.2 ⟨hy, hM y⟩, rfl⟩
    · by_contra hi
      exact hnone ⟨l, hmemI l (Finset.mem_Icc.1 hl).1 hi⟩
  let k := I.max' hInonempty
  have hk := Finset.mem_filter.1 (Finset.max'_mem I hInonempty)
  have hk₂ : 2 ≤ k := (Finset.mem_Icc.1 hk.1).1
  let E := {y | k < size y}
  have hE : E.Finite := by
    apply ((Finset.Ioc k M).finite_toSet.biUnion
      (t := fun l => {y | size y = l}) (fun l hl => ?_)).subset
    · intro y hy
      exact mem_iUnion₂.2 ⟨size y, Finset.mem_Ioc.2 ⟨hy, hM y⟩, rfl⟩
    · by_contra hi
      have hkl := (Finset.mem_Ioc.1 hl).1
      exact hkl.not_ge (Finset.le_max' I l (hmemI l (hk₂.trans hkl.le) hi))
  let : Infinite {y | size y = k} := hk.2.to_subtype
  let y : ℕ → {y | size y = k} := Infinite.natEmbedding _
  have hy : Injective y := (Infinite.natEmbedding _).injective
  let e (n : ℕ) : Fin k ≃ (q ⁻¹' {(y n).1} : Set K) :=
    letI := (hfin (y n).1).to_subtype
    (Finite.equivFinOfCardEq (y n).2).symm
  let x (i : Fin k) (n : ℕ) : K := (e n i).1
  have hx (i : Fin k) (n : ℕ) : q (x i n) = (y n).1 := (e n i).2
  let i₀ : Fin k := ⟨0, by omega⟩
  let i₁ : Fin k := ⟨1, by omega⟩
  let : Nonempty (Fin k) := ⟨i₀⟩
  obtain ⟨σ, hσ, hsep⟩ := exists_subseq_pairwise_clopen_separation hG x
    (fun i j n m hnm he => hnm (hy (Subtype.ext
      ((hx i n).symm.trans ((congrArg q he).trans (hx j m))))))
    (fun i j hij => Eventually.of_forall fun n h => hij ((e n).injective (Subtype.ext h)))
  have hsep' (i j : Fin k) : ∃ U : Set K, IsClopen U ∧
      ∀ᶠ n in atTop, x i (σ n) ∈ U ∧ (i ≠ j → x j (σ n) ∉ U) := by
    by_cases hij : i = j
    · exact ⟨univ, isClopen_univ, Eventually.of_forall fun _ => ⟨mem_univ _, by simp [hij]⟩⟩
    obtain ⟨U, hU, he⟩ := hsep i j hij
    exact ⟨U, hU, he.mono fun _ h => ⟨h.1, fun _ => h.2⟩⟩
  choose U hU hsepU using hsep'
  let D (i : Fin k) := ⋂ j, U i j ∩ (if j = i then univ else (U j i)ᶜ)
  have hD (i : Fin k) : IsClopen (D i) :=
    isClopen_iInter_of_finite fun j => (hU i j).inter (by
      split
      · exact isClopen_univ
      · exact (hU j i).compl)
  have hd : Pairwise (fun i j => Disjoint (D i) (D j)) := by
    intro i j hij
    apply Set.disjoint_left.2
    intro z hi hj
    have hzi := (mem_iInter.1 hi j).1
    have hzj := (mem_iInter.1 hj i).2
    exact (by simpa only [ite_eq_right hij, mem_compl_iff] using hzj : z ∉ U i j) hzi
  have ht : ∀ᶠ n in atTop, ∀ i, x i (σ n) ∈ D i := by
    filter_upwards [eventually_all.2 (fun i => eventually_all.2 (hsepU i))] with n hn i
    apply mem_iInter.2
    intro j
    refine ⟨(hn i j).1, ?_⟩
    by_cases hij : j = i
    · simp [hij]
    · simpa only [ite_eq_right hij, mem_compl_iff] using (hn j i).2 hij
  let P := ⋂ i, q '' D i
  have hPc : IsClosed P :=
    isClosed_iInter fun i => ((hD i).isClosed.isCompact.image hq).isClosed
  have hP : IsCompact P := by
    refine ((hD i₀).isClosed.isCompact.image hq).of_isClosed_subset hPc ?_
    exact iInter_subset _ i₀
  let : CompactSpace P := isCompact_iff_compactSpace.mp hP
  obtain ⟨N, hN⟩ := eventually_atTop.1 ht
  let z (n : ℕ) : P := ⟨(y (σ (N + n))).1, mem_iInter.2 fun i =>
    ⟨x i (σ (N + n)), hN _ (Nat.le_add_right N n) i, hx i _⟩⟩
  have hz : Injective (fun n => (z n).1) := by
    intro n m heq
    have h := hσ.injective (hy (Subtype.ext heq))
    omega
  have hclus : ∃ p : P, MapClusterPt p atTop z ∧ (p : Y) ∉ E := by
    by_contra! hbad
    have hfinite : {p : P | MapClusterPt p atTop z}.Finite :=
      (hE.preimage Subtype.val_injective.injOn).subset (fun p hp => hbad p hp)
    obtain ⟨p, τ, hτ, hc⟩ := exists_subseq_tendsto_of_finite_cluster z hfinite
    exact no_injective_limit_of_finite_fibres q hq hfin hseq
      (fun n => (z (τ n)).1) (hz.comp hτ.injective)
      (fun n => ⟨x i₀ _, hx i₀ _⟩) p.1 ((continuous_subtype_val.continuousAt : ContinuousAt Subtype.val p).tendsto.comp hc)
  obtain ⟨p, hp, hpE⟩ := hclus
  obtain ⟨C₀, hC₀, hC₀closed, hC₀sub⟩ := exists_mem_nhds_isClosed_subset
    ((hE.isClosed.isOpen_compl.preimage continuous_subtype_val).mem_nhds hpE)
  let C : Set Y := Subtype.val '' C₀
  have hCc : IsClosed C := (hC₀closed.isCompact.image continuous_subtype_val).isClosed
  have hCP : C ⊆ P := fun _ ⟨p, _, he⟩ => he ▸ p.2
  have hCsize (u : C) : size u.1 ≤ k := by
    obtain ⟨j, hj, he⟩ := u.2
    have hne := hC₀sub hj
    change ¬ k < size j.1 at hne
    exact he ▸ Nat.le_of_not_gt hne
  have hCi : C.Infinite := by
    obtain ⟨τ, hτ, hτC⟩ := extraction_of_frequently_atTop (hp.frequently hC₀)
    exact (infinite_range_of_injective (hz.comp hτ.injective)).mono
      (by rintro _ ⟨n, rfl⟩; exact ⟨z (τ n), hτC n, rfl⟩)
  let A (i : Fin k) := D i ∩ q ⁻¹' C
  have hAc (i : Fin k) : IsClosed (A i) := (hD i).isClosed.inter (hCc.preimage hq)
  have home (i : Fin k) : Nonempty (A i ≃ₜ C) := by
    let Q : A i → C := fun a => ⟨q a.1, a.2.2⟩
    have hQc : Continuous Q := (hq.comp continuous_subtype_val).subtype_mk _
    have hQs : Surjective Q := by
      intro u
      obtain ⟨a, ha, he⟩ := mem_iInter.1 (hCP u.2) i
      have haC : q a ∈ C := he.symm ▸ u.2
      exact ⟨⟨a, ha, haC⟩, Subtype.ext he⟩
    have hQi : Injective Q := by
      intro a b hab
      let u := Q a
      have hbu : q b.1 = u.1 := (congrArg Subtype.val hab).symm
      have hmeet (j : Fin k) : ∃ t : (q ⁻¹' {u.1} : Set K), t.1 ∈ D j := by
        obtain ⟨d, hd, he⟩ := mem_iInter.1 (hCP u.2) j
        exact ⟨⟨d, he⟩, hd⟩
      choose t ht using hmeet
      let s (j : Fin k) := if j = i then (⟨a.1, rfl⟩ : (q ⁻¹' {u.1} : Set K)) else t j
      have hs (j : Fin k) : (s j).1 ∈ D j := by
        by_cases hj : j = i
        · subst j
          simpa [s] using a.2.1
        · simpa [s, hj] using ht j
      have hsi : Injective s := by
        intro j l h
        by_contra hne
        exact Set.disjoint_left.1 (hd hne) (hs j) (h ▸ hs l)
      let := (hfin u.1).to_subtype
      have hsurj : Surjective s := hsi.bijective_of_nat_card_le (by
        rw [Nat.card_fin]
        exact hCsize u) |>.2
      obtain ⟨j, hj⟩ := hsurj ⟨b.1, hbu⟩
      have hji : j = i := by
        by_contra hne
        have he := congrArg Subtype.val hj
        exact Set.disjoint_left.1 (hd hne) (hs j) (he ▸ b.2.1)
      subst j
      exact Subtype.ext (by simpa [s] using congrArg Subtype.val hj)
    let : CompactSpace (A i) := isCompact_iff_compactSpace.mp (hAc i).isCompact
    exact ⟨(Equiv.ofBijective Q ⟨hQi, hQs⟩).toHomeomorphOfContinuousClosed hQc
      hQc.isClosedMap⟩
  obtain ⟨e₀⟩ := home i₀
  obtain ⟨e₁⟩ := home i₁
  have hi : i₀ ≠ i₁ := by
    intro he
    exact Nat.zero_ne_one (congrArg Fin.val he)
  have hdis : Disjoint (A i₀) (A i₁) := (hd hi).mono inter_subset_left inter_subset_left
  have hfinite := (hcopy _ _ (hAc i₀) (e₀.trans e₁.symm) hdis).1
  let : Finite (A i₀) := hfinite.to_subtype
  let : Finite C := Finite.of_surjective e₀ e₀.surjective
  exact hCi (Set.toFinite C)

open scoped Cardinal in
/-- Every continuous finite-to-one map from the actual CH Talagrand compactum
has a uniform fibre bound and only finitely many nonsingleton fibres. -/
theorem actual_finite_to_one
    (hCH : Cardinal.continuum.{0} = ℵ₁)
    (q : (SignedOrdinalRealization.finalPrefix hCH).LimitSpace → Y)
    (hq : Continuous q) (hfin : ∀ y : Y, (q ⁻¹' {y}).Finite) :
    (∃ M : ℕ, ∀ y : Y, Nat.card (q ⁻¹' {y} : Set _) ≤ M) ∧
      {y : Y | 1 < Nat.card (q ⁻¹' {y} : Set _)}.Finite := by
  obtain ⟨_, _, hG, hseq⟩ := SignedBallHistoryEndpoints.actual_signed_ball_history_endpoints hCH
  obtain ⟨_, hcopy, _⟩ := ContinuousFiniteImageTail.actual_CH_finite_image_and_copy_obstructions hCH
  exact ⟨exists_uniform_fibre_bound hG q hq hfin,
    finite_nonsingleton_fibres_of_endpoints hG hseq hcopy q hq hfin⟩

end D5.S3.Topology.InverseLimit.TalagrandFiniteFibres
