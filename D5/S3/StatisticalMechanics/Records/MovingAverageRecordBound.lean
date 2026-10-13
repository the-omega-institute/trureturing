/- GID: D5/S3/StatisticalMechanics/Records/MovingAverageRecordBound
   generality: G
   mirror-B: D5/B/S3/StatisticalMechanics/Records/MovingAverageRecordBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Atomless two-term moving-average records satisfy Q_n <= 3/(2n). -/

/-
admission_basis: open-problem-resolution (#15864; Proved)
escape_witness: none (open-problem-resolution basis)
Direct frozen dependencies: none (pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/16029.
DTR reading: movingAverage_record_bound and result each report DTR-Unregistered (Observe).
proof_shape: eval_eq_graph_null: bind-only; consumer(s): edge_sum_eq_null; escape_witness: none.
proof_shape: edge_sum_eq_null: bind-only; consumer(s): cyclic_sum_pair_null; escape_witness: none.
proof_shape: finRotate_two_cycle_false: bind-only; consumer(s): cyclic_sum_pair_null;
  escape_witness: none.
proof_shape: finRotate_ne_self: bind-only; consumer(s): cyclic_sum_pair_null; escape_witness:
  none.
proof_shape: cyclicSum: bind-only; consumer(s): cyclic_sum_pair_null, maxAt, runnerUpAt,
  cyclicRecordEvent; escape_witness: none.
proof_shape: cyclic_sum_pair_null: content; consumer(s): cyclic_ties_null; escape_witness: none.
proof_shape: cyclicTieSet: bind-only; consumer(s): cyclic_ties_null, maxAt_uniform,
  cyclic_record_union_ties, cyclic_record_bound; escape_witness: none.
proof_shape: cyclic_ties_null: content; consumer(s): maxAt_uniform_noAtoms, cyclic_record_bound;
  escape_witness: none.
proof_shape: maxAt: bind-only; consumer(s): maxAt_uniform, runnerUpAt, cyclic_record_bound;
  escape_witness: none.
proof_shape: maxAt_measurable: bind-only; consumer(s): maxAt_uniform, runnerUpAt_measurable;
  escape_witness: none.
proof_shape: maxAt_disjoint: bind-only; consumer(s): maxAt_uniform; escape_witness: none.
proof_shape: maxAt_rotate_preimage: bind-only; consumer(s): maxAt_uniform; escape_witness: none.
proof_shape: maxAt_uniform: content; consumer(s): maxAt_uniform_noAtoms; escape_witness: none.
proof_shape: maxAt_uniform_noAtoms: content; consumer(s): cyclic_record_bound; escape_witness:
  none.
proof_shape: runnerUpAt: bind-only; consumer(s): runnerUpAt_perm_preimage, cyclic_record_bound;
  escape_witness: none.
proof_shape: cyclicRecordEvent: bind-only; consumer(s): cyclic_record_union_ties,
  cyclic_record_bound, recordProb_eq_cyclic; escape_witness: none.
proof_shape: runnerUpAt_measurable: bind-only; consumer(s): runnerUpAt_reflection_measure,
  cyclic_record_bound; escape_witness: none.
proof_shape: edge_id: bind-only; consumer(s): cyclicSum_rev; escape_witness: none.
proof_shape: cyclicSum_rev: bind-only; consumer(s): runnerUpAt_rev_preimage; escape_witness: none.
proof_shape: runnerUpAt_perm_preimage: bind-only; consumer(s): runnerUpAt_rev_preimage;
  escape_witness: none.
proof_shape: runnerUpAt_rev_preimage: bind-only; consumer(s): runnerUpAt_reflection_measure;
  escape_witness: none.
proof_shape: cyclic_record_subset: bind-only; consumer(s): cyclic_record_union_ties;
  escape_witness: none.
proof_shape: runnerUpAt_disjoint: bind-only; consumer(s): cyclic_record_bound; escape_witness:
  none.
proof_shape: runnerUpAt_reflection_measure: bind-only; consumer(s): cyclic_record_bound;
  escape_witness: none.
proof_shape: cyclic_record_union_ties: bind-only; consumer(s): cyclic_record_bound;
  escape_witness: none.
proof_shape: maxAt_runnerUpAt_disjoint: bind-only; consumer(s): cyclic_record_bound;
  escape_witness: none.
proof_shape: cyclic_record_bound: content; consumer(s): movingAverage_record_bound;
  escape_witness: none.
proof_shape: recordProb: bind-only; consumer(s): claim, recordProb_eq_cyclic,
  movingAverage_record_bound; escape_witness: none.
proof_shape: claim: bind-only; consumer(s): result; escape_witness: none.
proof_shape: finRotate_mk_next: bind-only; consumer(s): recordProb_eq_cyclic; escape_witness:
  none.
proof_shape: recordProb_eq_cyclic: bind-only; consumer(s): movingAverage_record_bound;
  escape_witness: none.
proof_shape: movingAverage_record_bound: content; consumer(s): result; escape_witness: none.
proof_shape: density_noAtoms: bind-only; consumer(s): result; escape_witness: none.
proof_shape: result: content; consumer(s): settling result; escape_witness: none.
The public atomless theorem supplies the density result; all other helpers are private.
The literal zero-based record event compares Y_n with Y_2,...,Y_(n-1).
Fin bounds use i.isLt before omega; NoAtoms is installed as NullSingletonClass internally.
Reversal is MeasurableEquiv.piCongrLeft with Fin.revPerm.-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
namespace D5.S3.StatisticalMechanics.Records.MovingAverageRecordBound

open scoped BigOperators
open MeasureTheory Set
noncomputable section
private lemma eval_eq_graph_null {n : ℕ} (hn : 0 < n) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : NoAtoms μ)
    (j : Fin n) (g : (∀ k : Subtype (fun k : Fin n => k ≠ j), ℝ) → ℝ)
    (hg : Measurable g) :
    (Measure.pi (fun _ : Fin n => μ))
      {x | x j = g (fun k => x k.1)} = 0 := by
  classical
  letI : NullSingletonClass μ := hμ
  let p : Fin n → Prop := fun k => k ≠ j
  letI : DecidablePred p := fun k => Classical.propDecidable (k ≠ j)
  have hj : ¬ p j := by simp [p]
  let q : Subtype (fun k : Fin n => ¬ p k) := ⟨j, hj⟩
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p
  let S : Set ((∀ k : Subtype p, ℝ) × (∀ k : Subtype (fun k : Fin n => ¬ p k), ℝ)) :=
    {z | z.2 q = g z.1}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact measurableSet_eq_fun (measurable_pi_apply q |>.comp measurable_snd)
      (hg.comp measurable_fst)
  have hpre : e ⁻¹' S = {x : (∀ k : Fin n, ℝ) | x j = g (fun k => x k.1)} := by
    ext x
    change ((e x).2 q = g (e x).1) ↔ (x j = g (fun k => x k.1))
    rfl
  have hmp := measurePreserving_piEquivPiSubtypeProd (μ := fun _ : Fin n => μ) (α := fun _ : Fin n => ℝ) p
  have hnull : ((Measure.pi (fun k : Subtype p => μ)).prod
      (Measure.pi (fun k : Subtype (fun k : Fin n => ¬ p k) => μ))) S = 0 := by
    rw [Measure.prod_apply hS]
    rw [lintegral_eq_zero_iff (measurable_measure_prodMk_left hS)]
    filter_upwards [] with u
    have hfiber : Prod.mk u ⁻¹' S = {v | v q = g u} := by
      ext v
      change (v q = g u) ↔ (v q = g u)
      rfl
    rw [hfiber]
    exact Measure.pi_hyperplane (fun k : Subtype (fun k : Fin n => ¬ p k) => μ) q (g u)
  calc
    _ = (Measure.pi (fun _ : Fin n => μ)) (e ⁻¹' S) := by rw [hpre]
    _ = ((Measure.pi (fun k : Subtype p => μ)).prod
      (Measure.pi (fun k : Subtype (fun k : Fin n => ¬ p k) => μ))) S :=
      hmp.measure_preimage hS.nullMeasurableSet
    _ = 0 := hnull

private lemma edge_sum_eq_null {n : ℕ} (hn : 0 < n) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : NoAtoms μ)
    (a b c d : Fin n) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) :
    (Measure.pi (fun _ : Fin n => μ)) {x | x a + x b = x c + x d} = 0 := by
  classical
  let p : Fin n → Prop := fun k => k ≠ a
  letI : DecidablePred p := fun k => Classical.propDecidable (k ≠ a)
  have ha : ¬ p a := by simp [p]
  have hb : p b := by exact hab.symm
  have hc : p c := by exact hac.symm
  have hd : p d := by exact had.symm
  let g : (∀ k : Subtype p, ℝ) → ℝ := fun u => u ⟨c, hc⟩ + u ⟨d, hd⟩ - u ⟨b, hb⟩
  have hg : Measurable g := by
    fun_prop
  have hz := eval_eq_graph_null hn μ hμ a g hg
  have heq : {x : Fin n → ℝ | x a = g (fun k => x k.1)} =
      {x : Fin n → ℝ | x a + x b = x c + x d} := by
    ext x
    change (x a = x c + x d - x b) ↔ (x a + x b = x c + x d)
    constructor <;> intro h <;> linarith
  rw [← heq]
  exact hz
private lemma finRotate_two_cycle_false {n : ℕ} (hn : 3 ≤ n) (i j : Fin n)
    (hij : i ≠ j) (hijr : i = finRotate n j) (hrij : finRotate n i = j) : False := by
  let f : Equiv.Perm (Fin n) := finRotate n
  have hcycle : f.IsCycle := by
    dsimp [f]
    exact isCycle_finRotate_of_le (by omega)
  have hne : f i ≠ i := by
    intro h
    have hsupp : i ∉ f.support := by simpa [Equiv.Perm.mem_support] using h
    have hall : f.support = Finset.univ := by
      dsimp [f]
      exact support_finRotate_of_le (by omega)
    have : i ∈ f.support := by rw [hall]; simp
    contradiction
  have hpowi : (f ^ 2) i = i := by
    change f (f i) = i
    rw [hrij, hijr]
  have hpow : f ^ 2 = 1 := (hcycle.pow_eq_one_iff' hne).2 hpowi
  have hdvd : orderOf f ∣ 2 := orderOf_dvd_of_pow_eq_one hpow
  have hord : orderOf f = n := by
    rw [hcycle.orderOf, support_finRotate_of_le (by omega), Finset.card_univ, Fintype.card_fin]
  have hnle : n ≤ 2 := by
    apply Nat.le_of_dvd (by omega)
    simpa [hord] using hdvd
  omega
private lemma finRotate_ne_self {n : ℕ} (hn : 2 ≤ n) (i : Fin n) : finRotate n i ≠ i := by
  intro h
  have hcycle : (finRotate n).IsCycle := isCycle_finRotate_of_le hn
  have hsupp : i ∈ (finRotate n).support := by
    rw [support_finRotate_of_le hn]
    simp
  have hnot : i ∉ (finRotate n).support := by
    simpa [Equiv.Perm.mem_support] using h
  exact hnot hsupp


private def cyclicSum {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ℝ :=
  x i + x (finRotate n i)

private lemma cyclic_sum_pair_null {n : ℕ} (hn : 3 ≤ n) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : NoAtoms μ)
    (i j : Fin n) (hij : i ≠ j) :
    (Measure.pi (fun _ : Fin n => μ)) {x | cyclicSum x i = cyclicSum x j} = 0 := by
  classical
  by_cases hrot : i = finRotate n j
  · have hri_ne_i : finRotate n i ≠ i := finRotate_ne_self (by omega) i
    have hri_ne_j : finRotate n i ≠ j := by
      intro h
      exact finRotate_two_cycle_false hn i j hij hrot h
    have hri_ne_rj : finRotate n i ≠ finRotate n j := by
      intro h
      apply hri_ne_i
      calc
        finRotate n i = finRotate n j := h
        _ = i := hrot.symm
    have hz := edge_sum_eq_null (n := n) (μ := μ) (hn := by omega) hμ
      (finRotate n i) i j (finRotate n j) hri_ne_i hri_ne_j hri_ne_rj
    have heq : {x : Fin n → ℝ | x (finRotate n i) + x i = x j + x (finRotate n j)} =
        {x : Fin n → ℝ | cyclicSum x i = cyclicSum x j} := by
      ext x
      change (x (finRotate n i) + x i = x j + x (finRotate n j)) ↔
        (x i + x (finRotate n i) = x j + x (finRotate n j))
      constructor <;> intro h <;> linarith
    rw [← heq]
    exact hz
  · have hri_ne_i : i ≠ finRotate n i := (finRotate_ne_self (by omega) i).symm
    have hz := edge_sum_eq_null (n := n) (μ := μ) (hn := by omega) hμ
      i (finRotate n i) j (finRotate n j) hri_ne_i hij hrot
    exact hz

private def cyclicTieSet (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∃ i j : Fin n, i ≠ j ∧ cyclicSum x i = cyclicSum x j}

private lemma cyclic_ties_null {n : ℕ} (hn : 3 ≤ n) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : NoAtoms μ) :
    (Measure.pi (fun _ : Fin n => μ)) (cyclicTieSet n) = 0 := by
  classical
  have hzero : ∀ i j : Fin n,
      (Measure.pi (fun _ : Fin n => μ))
        (if i = j then (∅ : Set (Fin n → ℝ)) else {x | cyclicSum x i = cyclicSum x j}) = 0 := by
    intro i j
    by_cases h : i = j
    · simp [h]
    · simp [h, cyclic_sum_pair_null hn μ hμ i j h]
  have hun : cyclicTieSet n = ⋃ i : Fin n, ⋃ j : Fin n,
      (if i = j then (∅ : Set (Fin n → ℝ)) else {x | cyclicSum x i = cyclicSum x j}) := by
    ext x
    simp [cyclicTieSet]
  rw [hun]
  apply measure_iUnion_null
  intro i
  apply measure_iUnion_null
  intro j
  exact hzero i j

private def maxAt {n : ℕ} (k : Fin n) : Set (Fin n → ℝ) := {x | ∀ j, j ≠ k → cyclicSum x j < cyclicSum x k}

private lemma maxAt_measurable {n : ℕ} (k : Fin n) : MeasurableSet (maxAt k) := by
  have heq : maxAt k = ⋂ (j : Fin n), ⋂ (_hj : j ≠ k), {x : Fin n → ℝ | cyclicSum x j < cyclicSum x k} := by
    ext x; simp [maxAt]
  rw [heq]
  refine MeasurableSet.iInter (fun (j : Fin n) => ?_)
  refine MeasurableSet.iInter (fun (_hj : j ≠ k) => ?_)
  have hmeas (a : Fin n) : Measurable (fun x : Fin n → ℝ => cyclicSum x a) := by
    unfold cyclicSum; fun_prop
  exact measurableSet_lt (hmeas j) (hmeas k)

private lemma maxAt_disjoint {n : ℕ} {i j : Fin n} (hij : i ≠ j) : Disjoint (maxAt i) (maxAt j) := by
  rw [Set.disjoint_left]
  intro x hi hj
  exact (lt_asymm (hi j hij.symm) (hj i hij))

private lemma maxAt_rotate_preimage {n : ℕ} (hn : 0 < n) (k : Fin n) :
    let e := MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (finRotate n)
    e ⁻¹' maxAt k = maxAt ((finRotate n).symm k) := by
  dsimp
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let f : Equiv.Perm (Fin n) := finRotate n
  have hcyc (x : Fin n → ℝ) (a : Fin n) :
      cyclicSum ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (finRotate n)) x) a =
        cyclicSum x ((finRotate n).symm a) := by
    simp [cyclicSum, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  ext x
  constructor
  · intro h j hj
    have h' := h (f j)
    have hne : f j ≠ k := by
      intro hh
      exact hj (by
        have hsj := congrArg f.symm hh
        simpa only [Equiv.symm_apply_apply] using hsj)
    have hh := h' hne
    calc
      cyclicSum x j = cyclicSum ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) f) x) (f j) := by
        simpa [f, Equiv.symm_apply_apply] using (hcyc x (f j)).symm
      _ < cyclicSum ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) f) x) k := hh
      _ = cyclicSum x (f.symm k) := by simpa [f] using hcyc x k
  · intro h j hj
    have h' := h (f.symm j)
    have hne : f.symm j ≠ f.symm k := by
      intro hh
      have hjk : j = k := by
        have hsj := congrArg f hh
        simpa only [Equiv.apply_symm_apply] using hsj
      exact hj hjk
    have hh := h' hne
    calc
      cyclicSum ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) f) x) j = cyclicSum x (f.symm j) := by simpa [f] using hcyc x j
      _ < cyclicSum x (f.symm k) := hh
      _ = cyclicSum ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) f) x) k := by simpa [f] using (hcyc x k).symm

private lemma maxAt_uniform {n : ℕ} (hn : 0 < n) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (htie : (Measure.pi (fun _ : Fin n => μ)) (cyclicTieSet (n := n)) = 0) :
    ∀ k : Fin n, (Measure.pi (fun _ : Fin n => μ)) (maxAt k) = (1 : ENNReal) / n := by
  classical
  let M : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => μ)
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let f : Equiv.Perm (Fin n) := finRotate n
  have hmp := measurePreserving_piCongrLeft (μ := fun _ : Fin n => μ) (f := f)
  have hstep (k : Fin n) : M (maxAt (f k)) = M (maxAt k) := by
    have h := hmp.measure_preimage (maxAt_measurable (f k)).nullMeasurableSet
    rw [maxAt_rotate_preimage hn (f k)] at h
    simpa [M, f] using h.symm
  have hconst : ∀ k : Fin n, M (maxAt k) = M (maxAt 0) := by
    intro k
    have hiter : ∀ r : ℕ, M (maxAt ((f ^[r]) 0)) = M (maxAt 0) := by
      intro r
      induction r with
      | zero => simp
      | succ r ih =>
          rw [Function.iterate_succ_apply']
          exact (hstep _).trans ih
    have hk : (f ^[k.val]) 0 = k := by
      rw [← finCycle_eq_finRotate_iterate (k := k)]
      simp [finCycle]
    rw [← hk]
    exact hiter k.val
  have hsum : ∑ k : Fin n, M (maxAt k) = 1 := by
    have hdis : (↑(Finset.univ : Finset (Fin n)) : Set (Fin n)).PairwiseDisjoint maxAt := by
      intro i hi j hj hij
      exact maxAt_disjoint hij
    have hmeas : ∀ k ∈ (Finset.univ : Finset (Fin n)), MeasurableSet (maxAt k) := by
      intro k hk; exact maxAt_measurable k
    have hb := MeasureTheory.measure_biUnion_finset (μ := M) hdis hmeas
    have hcomp : (⋃ k : Fin n, maxAt k)ᶜ ⊆ (cyclicTieSet (n := n) : Set (Fin n → ℝ)) := by
      intro x hx
      obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) (cyclicSum x) Finset.univ_nonempty
      have hnotmax : x ∉ maxAt k := by
        intro hmem
        exact hx (by exact mem_iUnion.2 ⟨k, hmem⟩)
      change ¬ (∀ j, j ≠ k → cyclicSum x j < cyclicSum x k) at hnotmax
      push_neg at hnotmax
      obtain ⟨j, hj, hjnot⟩ := hnotmax
      have hle := hmax j (by simp)
      have heq : cyclicSum x j = cyclicSum x k := le_antisymm hle hjnot
      exact ⟨j, k, hj, heq⟩
    have hUmeas : MeasurableSet (⋃ k : Fin n, maxAt k) := by
      exact MeasurableSet.iUnion (fun k => maxAt_measurable k)
    have hcompnull : M ((⋃ k : Fin n, maxAt k)ᶜ) = 0 :=
      measure_mono_null hcomp (by simpa [M] using htie)
    have hcompl := measure_compl hUmeas (by simp [M] : M (⋃ k : Fin n, maxAt k) ≠ ⊤)
    have hc0 : (1 : ENNReal) - M (⋃ k : Fin n, maxAt k) = 0 := by
      have hzero := hcompnull
      rw [hcompl] at hzero
      simpa [M] using hzero
    have hleone : (1 : ENNReal) ≤ M (⋃ k : Fin n, maxAt k) := tsub_eq_zero_iff_le.mp hc0
    have hU : M (⋃ k : Fin n, maxAt k) = 1 := by
      apply le_antisymm
      · calc
          M (⋃ k : Fin n, maxAt k) ≤ M Set.univ := measure_mono (subset_univ _)
          _ = 1 := by simp [M]
      · exact hleone
    have hb' : M (⋃ k : Fin n, maxAt k) = ∑ k : Fin n, M (maxAt k) := by
      simpa using hb
    rw [← hb']
    exact hU
  have hval : M (maxAt 0) = (1 : ENNReal) / n := by
    have hsum' : ∑ k : Fin n, M (maxAt 0) = 1 := by
      simpa [hconst] using hsum
    have hn0 : n ≠ 0 := by omega
    exact (ENNReal.eq_div_iff (a := (n : ENNReal)) (b := M (maxAt 0)) (c := 1)
      (by exact_mod_cast hn0) (by simp)).2 (by
      simpa [Finset.sum_const, nsmul_eq_mul] using hsum')
  intro k
  rw [hconst k, hval]

private theorem maxAt_uniform_noAtoms {n : ℕ} (hn : 3 ≤ n) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : NoAtoms μ) :
    ∀ k : Fin n, (Measure.pi (fun _ : Fin n => μ)) (maxAt k) = (1 : ENNReal) / n := by
  exact maxAt_uniform (by omega) μ (cyclic_ties_null hn μ hμ)

private def runnerUpAt {n : ℕ} (max second : Fin n) : Set (Fin n → ℝ) :=
  {x | x ∈ maxAt max ∧ ∀ j, j ≠ max → j ≠ second → cyclicSum x j < cyclicSum x second}

private def cyclicRecordEvent {n : ℕ} (hn : 3 ≤ n) : Set (Fin n → ℝ) :=
  {x | ∀ j : Fin n, j.val ≤ n - 3 → cyclicSum x j < cyclicSum x ⟨n - 2, by omega⟩}


private lemma runnerUpAt_measurable {n : ℕ} (m s : Fin n) : MeasurableSet (runnerUpAt m s) := by
  have hmeas (a : Fin n) : Measurable (fun x : Fin n → ℝ => cyclicSum x a) := by
    unfold cyclicSum; fun_prop
  have hmax : MeasurableSet (maxAt m) := maxAt_measurable m
  have hrest : MeasurableSet {x : Fin n → ℝ | ∀ j, j ≠ m → j ≠ s → cyclicSum x j < cyclicSum x s} := by
    have heq : {x : Fin n → ℝ | ∀ j, j ≠ m → j ≠ s → cyclicSum x j < cyclicSum x s} =
        ⋂ (j : Fin n), ⋂ (_hm : j ≠ m), ⋂ (_hs : j ≠ s),
          {x : Fin n → ℝ | cyclicSum x j < cyclicSum x s} := by
      ext x; simp
    rw [heq]
    refine MeasurableSet.iInter (fun j => ?_)
    refine MeasurableSet.iInter (fun _hm => ?_)
    refine MeasurableSet.iInter (fun _hs => ?_)
    exact measurableSet_lt (hmeas j) (hmeas s)
  exact hmax.inter hrest

private lemma edge_id {n : ℕ} (hn : 0 < n) (i : Fin n) :
    finRotate n (Fin.rev (finRotate n i)) = Fin.rev i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  by_cases hi : i = Fin.last k
  · subst i
    simp [finRotate_last, Fin.rev_zero, Fin.rev_last]
  · have hrot : (finRotate (k+1) i : ℕ) = i + 1 := coe_finRotate_of_ne_last hi
    have hri : Fin.rev (finRotate (k+1) i) ≠ Fin.last k := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_rev, Fin.val_last] at hv
      rw [hrot] at hv
      have hi' := i.isLt
      omega
    apply Fin.ext
    rw [coe_finRotate_of_ne_last hri]
    simp only [Fin.val_rev]
    rw [hrot]
    have hi' := i.isLt
    omega

private lemma cyclicSum_rev {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (i : Fin n) :
    cyclicSum ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (Fin.revPerm : Equiv.Perm (Fin n))) x) i =
      cyclicSum x ((((Fin.revPerm : Equiv.Perm (Fin n)) * (finRotate n : Equiv.Perm (Fin n)))) i) := by
  have hcoord (j : Fin n) :
      ((MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (Fin.revPerm : Equiv.Perm (Fin n))) x) j = x j.rev := by
    have h := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℝ) (Fin.revPerm : Equiv.Perm (Fin n)) x j.rev
    simpa only [Fin.revPerm_apply, Fin.rev_rev] using h
  unfold cyclicSum
  rw [hcoord, hcoord]
  simp only [Equiv.Perm.mul_apply, Fin.revPerm_apply]
  rw [edge_id hn]
  exact add_comm _ _

private lemma runnerUpAt_perm_preimage {n : ℕ} (e : (Fin n → ℝ) → (Fin n → ℝ))
    (g : Equiv.Perm (Fin n))
    (hcyc : ∀ x i, cyclicSum (e x) i = cyclicSum x (g i)) (m s : Fin n) :
    e ⁻¹' runnerUpAt m s = runnerUpAt (g m) (g s) := by
  ext x
  constructor
  · intro h
    change e x ∈ maxAt m ∧ ∀ j, j ≠ m → j ≠ s → cyclicSum (e x) j < cyclicSum (e x) s at h
    constructor
    · intro j hj
      have hj' : g.symm j ≠ m := by
        intro heq
        apply hj
        calc
          j = g (g.symm j) := (g.apply_symm_apply j).symm
          _ = g m := congrArg g heq
      have hh := h.1 (g.symm j) hj'
      rw [hcyc, hcyc] at hh
      simpa using hh
    · intro j hjm hjs
      have hj'm : g.symm j ≠ m := by
        intro heq
        apply hjm
        calc
          j = g (g.symm j) := (g.apply_symm_apply j).symm
          _ = g m := congrArg g heq
      have hj's : g.symm j ≠ s := by
        intro heq
        apply hjs
        calc
          j = g (g.symm j) := (g.apply_symm_apply j).symm
          _ = g s := congrArg g heq
      have hh := h.2 (g.symm j) hj'm hj's
      rw [hcyc, hcyc] at hh
      simpa using hh
  · intro h
    change x ∈ maxAt (g m) ∧ ∀ j, j ≠ g m → j ≠ g s → cyclicSum x j < cyclicSum x (g s) at h
    constructor
    · intro j hj
      rw [hcyc, hcyc]
      exact h.1 (g j) (fun heq => hj (g.injective heq))
    · intro j hjm hjs
      rw [hcyc, hcyc]
      exact h.2 (g j) (fun heq => hjm (g.injective heq)) (fun heq => hjs (g.injective heq))

private lemma runnerUpAt_rev_preimage {n : ℕ} (hn : 3 ≤ n) :
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) (Fin.revPerm : Equiv.Perm (Fin n))) ⁻¹'
      runnerUpAt (⟨n-1, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n) =
    runnerUpAt (⟨n-1, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n) := by
  let g : Equiv.Perm (Fin n) := (Fin.revPerm : Equiv.Perm (Fin n)) * (finRotate n : Equiv.Perm (Fin n))
  have hgm : g (⟨n-1, by omega⟩ : Fin n) = (⟨n-1, by omega⟩ : Fin n) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    change Fin.rev (finRotate (k+1) (Fin.last k)) = Fin.last k
    simp
  have hgp : g (⟨n-2, by omega⟩ : Fin n) = (⟨0, by omega⟩ : Fin n) := by
    apply Fin.ext
    change n - ((finRotate n (⟨n-2, by omega⟩ : Fin n)).val + 1) = 0
    have hrot : (finRotate n (⟨n-2, by omega⟩ : Fin n)).val = n-1 := by
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      rw [coe_finRotate_of_ne_last (by intro h; have hv := congrArg Fin.val h; simp at hv; omega)]
      simp; omega
    rw [hrot]; omega
  rw [runnerUpAt_perm_preimage _ g (cyclicSum_rev (by omega)), hgm, hgp]

private lemma cyclic_record_subset {n : ℕ} (hn : 3 ≤ n) :
    cyclicRecordEvent hn ⊆
      maxAt (⟨n - 2, by omega⟩ : Fin n) ∪
      runnerUpAt (⟨n - 1, by omega⟩ : Fin n) (⟨n - 2, by omega⟩ : Fin n) ∪
      (cyclicTieSet n) := by
  intro x hx
  let p : Fin n := ⟨n - 2, by omega⟩
  let m : Fin n := ⟨n - 1, by omega⟩
  change (∀ j : Fin n, j.val ≤ n - 3 → cyclicSum x j < cyclicSum x p) at hx
  simp only [mem_union]
  rw [or_assoc]
  change (x ∈ maxAt p ∨ x ∈ runnerUpAt m p ∨ x ∈ (cyclicTieSet n))
  by_cases hlt : cyclicSum x m < cyclicSum x p
  · left
    intro j hj
    by_cases hjp : j = p
    · exact False.elim (hj hjp)
    by_cases hjm : j = m
    · simpa [hjm] using hlt
    have hjlow : j.val ≤ n - 3 := by
      have hjlt : j.val < n := j.isLt
      have hjpval : j.val ≠ n - 2 := by
        intro hv
        apply hjp
        apply Fin.ext
        simpa [p] using hv
      have hjmval : j.val ≠ n - 1 := by
        intro hv
        apply hjm
        apply Fin.ext
        simpa [m] using hv
      omega
    exact hx j hjlow
  · by_cases heq : cyclicSum x m = cyclicSum x p
    · right; right
      change ∃ i j : Fin n, i ≠ j ∧ cyclicSum x i = cyclicSum x j
      have hmp : m ≠ p := by
        intro h
        have hv := congrArg Fin.val h
        simp [m, p] at hv
        omega
      exact ⟨m, p, hmp, heq⟩
    · have hgt : cyclicSum x p < cyclicSum x m := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
      right; left
      change x ∈ maxAt m ∧ ∀ j, j ≠ m → j ≠ p → cyclicSum x j < cyclicSum x p
      constructor
      · intro j hj
        by_cases hjp : j = p
        · simpa [hjp] using hgt
        by_cases hjm : j = m
        · exact False.elim (hj hjm)
        have hjlow : j.val ≤ n - 3 := by
          have hjlt : j.val < n := j.isLt
          have hjpval : j.val ≠ n - 2 := by
            intro hv
            apply hjp
            apply Fin.ext
            simpa [p] using hv
          have hjmval : j.val ≠ n - 1 := by
            intro hv
            apply hjm
            apply Fin.ext
            simpa [m] using hv
          omega
        exact lt_trans (hx j hjlow) hgt
      · intro j hjm hjp
        exact hx j (by
          have hjlt : j.val < n := j.isLt
          have hjpval : j.val ≠ n - 2 := by
            intro hv
            apply hjp
            apply Fin.ext
            simpa [p] using hv
          have hjmval : j.val ≠ n - 1 := by
            intro hv
            apply hjm
            apply Fin.ext
            simpa [m] using hv
          omega)

private lemma runnerUpAt_disjoint {n : ℕ} {m s t : Fin n}
    (hsm : s ≠ m) (htm : t ≠ m) (hst : s ≠ t) :
    Disjoint (runnerUpAt m s) (runnerUpAt m t) := by
  rw [Set.disjoint_left]
  intro x hs ht
  exact lt_asymm (hs.2 t htm hst.symm) (ht.2 s hsm hst)

private lemma runnerUpAt_reflection_measure {n : ℕ} (hn : 3 ≤ n) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    (Measure.pi (fun _ : Fin n => μ)) (runnerUpAt (⟨n-1, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n)) =
    (Measure.pi (fun _ : Fin n => μ)) (runnerUpAt (⟨n-1, by omega⟩ : Fin n) (⟨0, by omega⟩ : Fin n)) := by
  have hmp := measurePreserving_piCongrLeft (μ := fun _ : Fin n => μ) (f := (Fin.revPerm : Equiv.Perm (Fin n)))
  have h := hmp.measure_preimage (runnerUpAt_measurable (⟨n-1, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n)).nullMeasurableSet
  rw [runnerUpAt_rev_preimage hn] at h
  exact h.symm

private lemma cyclic_record_union_ties {n : ℕ} (hn : 3 ≤ n) :
    cyclicRecordEvent hn ∪ (cyclicTieSet n) =
      maxAt (⟨n-2, by omega⟩ : Fin n) ∪
        runnerUpAt (⟨n-1, by omega⟩ : Fin n) (⟨n-2, by omega⟩ : Fin n) ∪ (cyclicTieSet n) := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with h | h
    · exact cyclic_record_subset hn h
    · exact Or.inr h
  · intro x hx
    rcases hx with (h | h) | h
    · left
      intro j hj
      exact h j (by intro heq; have hv := congrArg Fin.val heq; simp at hv; omega)
    · left
      intro j hj
      exact h.2 j (by intro heq; have hv := congrArg Fin.val heq; simp at hv; omega)
        (by intro heq; have hv := congrArg Fin.val heq; simp at hv; omega)
    · exact Or.inr h

private lemma maxAt_runnerUpAt_disjoint {n : ℕ} {p m : Fin n} (hpm : p ≠ m) :
    Disjoint (maxAt p) (runnerUpAt m p) := by
  rw [Set.disjoint_left]
  intro x ha hb
  exact lt_asymm (ha m hpm.symm) (hb.1 p hpm)

private lemma cyclic_record_bound {n : ℕ} (hn : 3 ≤ n) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (hμ : NoAtoms μ) :
    ((Measure.pi (fun _ : Fin n => μ)) (cyclicRecordEvent hn)).toReal ≤ 3 / (2 * n) := by
  let M : Measure (Fin n → ℝ) := Measure.pi (fun _ : Fin n => μ)
  let p : Fin n := ⟨n-2, by omega⟩
  let m : Fin n := ⟨n-1, by omega⟩
  let z : Fin n := ⟨0, by omega⟩
  have hpm : p ≠ m := by intro h; have hv := congrArg Fin.val h; simp [p, m] at hv; omega
  have hzm : z ≠ m := by intro h; have hv := congrArg Fin.val h; simp [z, m] at hv; omega
  have hpz : p ≠ z := by intro h; have hv := congrArg Fin.val h; simp [p, z] at hv; omega
  have hB : M (runnerUpAt m p) = M (runnerUpAt m z) := runnerUpAt_reflection_measure hn μ
  have hBsum : M (runnerUpAt m p) + M (runnerUpAt m p) ≤ (1 : ENNReal) / n := by
    calc
      _ = M (runnerUpAt m p ∪ runnerUpAt m z) := by
        rw [measure_union (runnerUpAt_disjoint hpm hzm hpz) (runnerUpAt_measurable m z), ← hB]
      _ ≤ M (maxAt m) := measure_mono (by intro x hx; rcases hx with h | h <;> exact h.1)
      _ = _ := maxAt_uniform_noAtoms hn μ hμ m
  have hR : M (cyclicRecordEvent hn) ≤ (1 : ENNReal) / n + M (runnerUpAt m p) := by
    calc
      _ ≤ M (cyclicRecordEvent hn ∪ (cyclicTieSet n)) := measure_mono Set.subset_union_left
      _ = M (maxAt p ∪ runnerUpAt m p ∪ (cyclicTieSet n)) := by
        rw [cyclic_record_union_ties hn]
      _ ≤ M (maxAt p ∪ runnerUpAt m p) + M (cyclicTieSet n) := measure_union_le _ _
      _ = M (maxAt p ∪ runnerUpAt m p) := by
        have hz : M (cyclicTieSet n) = 0 := cyclic_ties_null hn μ hμ
        rw [hz, add_zero]
      _ = M (maxAt p) + M (runnerUpAt m p) :=
        measure_union (maxAt_runnerUpAt_disjoint hpm) (runnerUpAt_measurable m p)
      _ = _ := by rw [maxAt_uniform_noAtoms hn μ hμ]
  have hfinite (S : Set (Fin n → ℝ)) : M S ≠ ⊤ := measure_ne_top _ _
  have hfrac : ((1 : ENNReal) / n) ≠ ⊤ := by finiteness
  have hBsum' := (ENNReal.toReal_le_toReal (by finiteness) hfrac).2 hBsum
  rw [ENNReal.toReal_add (hfinite _) (hfinite _), ENNReal.toReal_div] at hBsum'
  have hR' := (ENNReal.toReal_le_toReal (hfinite _) (by finiteness)).2 hR
  rw [ENNReal.toReal_add hfrac (hfinite _), ENNReal.toReal_div] at hR'
  simp only [ENNReal.toReal_one, ENNReal.toReal_natCast] at hBsum' hR'
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  change (M (cyclicRecordEvent hn)).toReal ≤ 3 / (2 * n)
  calc
    _ ≤ 1 / n + (M (runnerUpAt m p)).toReal := hR'
    _ ≤ 3 / (2 * n) := by
      have hid : (3 : ℝ) / (2 * n) = 1 / n + (1 / n) / 2 := by field_simp; ring
      rw [hid]
      linarith

noncomputable def recordProb (μ : Measure ℝ) (n : ℕ) : ℝ :=
  (Measure.pi (fun _ : Fin n => μ)
    {x | ∀ i : Fin n, 1 ≤ i.val → i.val + 2 ≤ n →
      x ⟨i.val - 1, by omega⟩ + x i <
      x ⟨n - 2, by have hi := i.isLt; omega⟩ + x ⟨n - 1, by have hi := i.isLt; omega⟩}).toReal

def claim : Prop := ∀ (f : ℝ → ℝ), Continuous f → (∀ x, 0 ≤ f x) →
    ∀ μ, μ = MeasureTheory.volume.withDensity (fun x => ENNReal.ofReal (f x)) →
      IsProbabilityMeasure μ → μ (Set.Iic 0) = 0 →
      ∀ n ≥ 3, recordProb μ n ≤ 3 / (2 * n)

private lemma finRotate_mk_next {n : ℕ} (i : Fin n) (hi : i.val + 1 < n) :
    finRotate n i = (⟨i.val + 1, hi⟩ : Fin n) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (by have h := i.isLt; omega : n ≠ 0)
  simpa using (finRotate_of_lt (n := k) (k := i.val) (by omega))

private lemma recordProb_eq_cyclic {n : ℕ} (hn : 3 ≤ n) (μ : Measure ℝ) :
    recordProb μ n = ((Measure.pi (fun _ : Fin n => μ)) (cyclicRecordEvent hn)).toReal := by
  unfold recordProb
  congr 2
  ext x
  have hterm : cyclicSum x (⟨n-2, by omega⟩ : Fin n) =
      x (⟨n-2, by omega⟩ : Fin n) + x (⟨n-1, by omega⟩ : Fin n) := by
    unfold cyclicSum
    rw [finRotate_mk_next _ (by simp; omega)]
    congr 1
    apply congrArg x
    apply Fin.ext
    simp; omega
  constructor
  · intro h j hj
    let i : Fin n := ⟨j.val + 1, by omega⟩
    have hi1 : 1 ≤ i.val := by simp [i]
    have hi2 : i.val + 2 ≤ n := by simp [i]; omega
    have hh := h i hi1 hi2
    have heq : (⟨i.val-1, by have hi := i.isLt; omega⟩ : Fin n) = j := by
      apply Fin.ext; simp [i]
    rw [heq] at hh
    change cyclicSum x j < cyclicSum x (⟨n-2, by omega⟩ : Fin n)
    rw [hterm]
    unfold cyclicSum
    rw [finRotate_mk_next j (by omega)]
    exact hh
  · intro h i hi1 hi2
    let j : Fin n := ⟨i.val-1, by have hi := i.isLt; omega⟩
    have hj : j.val ≤ n-3 := by simp [j]; omega
    have hh := h j hj
    change cyclicSum x j < cyclicSum x (⟨n-2, by omega⟩ : Fin n) at hh
    rw [hterm] at hh
    unfold cyclicSum at hh
    rw [finRotate_mk_next j (by simp [j]; omega)] at hh
    have heq : (⟨j.val+1, by simp [j]; omega⟩ : Fin n) = i := by
      apply Fin.ext; simp [j]; omega
    rw [heq] at hh
    exact hh

theorem movingAverage_record_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : NoAtoms μ) (n : ℕ) (hn : 3 ≤ n) :
    recordProb μ n ≤ 3 / (2 * n) := by
  rw [recordProb_eq_cyclic hn μ]
  exact cyclic_record_bound hn μ hμ

private theorem density_noAtoms (f : ℝ → ℝ) (μ : Measure ℝ)
    (hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (f x))) : NoAtoms μ := by
  rw [hμ]
  exact nullSingletonClass_withDensity _

theorem result : claim := by
  intro f _hf _hnonneg μ hμ hprob _hpos n hn
  letI := hprob
  exact movingAverage_record_bound μ (density_noAtoms f μ hμ) n hn


end

end D5.S3.StatisticalMechanics.Records.MovingAverageRecordBound
