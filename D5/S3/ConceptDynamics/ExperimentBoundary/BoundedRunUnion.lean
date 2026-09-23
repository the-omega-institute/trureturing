/- GID: D5/S3/ConceptDynamics/ExperimentBoundary/BoundedRunUnion
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/ExperimentBoundary/BoundedRunUnion
   mirror-E: none(waiver:no-numerical-evidence)
   anchors: []
   utility: none
   digest: Every finite prefix is realized in the dense null bounded-run union, whose inverse-limit comparison is not surjective. -/

import D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace

namespace D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
open D5.S3.ConceptDynamics.Experiment.InfiniteIdentificationFiniteInexactness
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates
open D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunSpace

noncomputable def boundaryUnit : NativeTheoremUnit bitArena where
  realization := bitRealization
  proof := by
    change Boundary (fun b : Bool => b)
    classical
    let read : Bool → Bool := fun b => b
    have hclosed (k : Nat) : IsClosed (bounded read k) := by
      have heq : bounded read k = ⋂ j : Nat, ⋃ i : Fin k, {x : Stream | x (j + i) = false} := by
        ext x
        simp [bounded, read]
      rw [heq]
      exact isClosed_iInter fun j => isClosed_iUnion_of_finite fun i =>
        isClosed_eq (continuous_apply (j + i)) continuous_const
    have hmono (k : Nat) : bounded read k ⊆ bounded read (k + 1) := by
      intro x hx j
      obtain ⟨i, hi⟩ := hx j
      exact ⟨⟨i, by omega⟩, hi⟩
    have hstrict (k : Nat) (hk : 2 ≤ k) : bounded read k ⊂ bounded read (k + 1) := by
      refine ssubset_iff_subset_ne.mpr ⟨hmono k, ?_⟩
      intro heq
      let x : Stream := fun j => decide (j < k)
      have hlarge : x ∈ bounded read (k + 1) := by
        intro j
        exact ⟨⟨k, by omega⟩, by simp [x, read]⟩
      rw [← heq] at hlarge
      obtain ⟨i, hi⟩ := hlarge 0
      simpa [x, read, i.isLt] using hi
    have hextend (k n : Nat) (hk : 0 < k) (w : Word n) (hw : w ∈ language read k n) :
        zeroExtend w ∈ bounded read k := by
      intro j
      by_cases h : j + k ≤ n
      · obtain ⟨i, hi⟩ := hw j h
        refine ⟨i, ?_⟩
        simpa [zeroExtend, read, show j + i.val < n by omega] using hi
      · refine ⟨⟨k - 1, by omega⟩, ?_⟩
        simp [zeroExtend, read, show ¬j + (k - 1) < n by omega]
    have hprefix (k n : Nat) (x : Stream) (hx : x ∈ bounded read k) :
        finiteTranscript n x ∈ language read k n := by
      intro j h
      obtain ⟨i, hi⟩ := hx j
      exact ⟨i, hi⟩
    have himage (k : Nat) (hk : 0 < k) (n : Nat) :
        finiteTranscript n '' bounded read k = language read k n := by
      apply subset_antisymm
      · rintro _ ⟨x, hx, rfl⟩; exact hprefix k n x hx
      · intro w hw
        refine ⟨zeroExtend w, hextend k n hk w hw, ?_⟩
        funext i
        simp [finiteTranscript, zeroExtend, i.isLt]
    have hfull (k n : Nat) (hn : n < k) : language read k n = univ := by
      ext w
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      intro j h
      omega
    have huimage (n : Nat) : finiteTranscript n '' union read = univ := by
      apply eq_univ_of_forall
      intro w
      have hn : n < max 2 (n + 1) := by omega
      have hw : w ∈ language read (max 2 (n + 1)) n := by rw [hfull _ _ hn]; trivial
      obtain ⟨x, hx, rfl⟩ := (himage (max 2 (n + 1)) (by omega) n).symm ▸ hw
      exact ⟨x, mem_iUnion.mpr ⟨_, mem_iUnion.mpr ⟨by omega, hx⟩⟩, rfl⟩
    have hunonempty : (union read).Nonempty := by
      refine ⟨fun _ => false, mem_iUnion.mpr ⟨2, mem_iUnion.mpr ⟨le_refl _, ?_⟩⟩⟩
      exact fun _ => ⟨⟨0, by omega⟩, rfl⟩
    have hproper : union read ⊂ univ := by
      refine ssubset_iff_subset_ne.mpr ⟨subset_univ _, ?_⟩
      intro heq
      have hx : (fun _ : Nat => true) ∈ union read := heq.symm ▸ mem_univ _
      rcases mem_iUnion.mp hx with ⟨k, hx⟩
      rcases mem_iUnion.mp hx with ⟨hk, hx⟩
      obtain ⟨i, hi⟩ := hx 0
      exact Bool.noConfusion hi
    have hdense : Dense (union read) := by
      intro x
      have hm (n : Nat) : zeroExtend (finiteTranscript n x) ∈ union read := by
        refine mem_iUnion.mpr ⟨max 2 (n + 1), mem_iUnion.mpr ⟨by omega, ?_⟩⟩
        apply hextend _ _ (by omega)
        rw [hfull _ _ (by omega)]; trivial
      apply mem_closure_of_tendsto (f := fun n => zeroExtend (finiteTranscript n x)) (b := atTop) ?_ (Eventually.of_forall hm)
      apply tendsto_pi_nhds.mpr
      intro j
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_gt_atTop j] with n hn
      simp [zeroExtend, finiteTranscript, hn]
    have hmeas : MeasurableSet (union read) :=
      MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun _ => (hclosed k).measurableSet
    have hfixed (k : Nat) (x : Stream) : x ∈ bounded read k ↔ prefixes x ∈ fixedLimit read k := by
      constructor
      · intro hx n; exact hprefix k n x hx
      · intro hx j
        obtain ⟨i, hi⟩ := hx (j + k) j (le_refl _)
        exact ⟨i, hi⟩
    have hthread (w : Threads) : prefixes (threadStream w) = w := by
      have hcoord (j n : Nat) (hjn : j < n) : w.val n ⟨j, hjn⟩ = threadStream w j := by
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show j + 1 ≤ n by omega)
        induction d with
        | zero => rfl
        | succ d ih =>
            have h := congrFun (w.property (j + 1 + d)) ⟨j, by omega⟩
            exact h.trans (ih (by omega))
      apply Subtype.ext
      funext n i
      exact (hcoord i n i.isLt).symm
    have hinjective : Function.Injective prefixes := by
      intro x y h
      funext j
      exact congrArg (fun w : Threads => w.val (j + 1) ⟨j, by omega⟩) h
    have hsource : prefixes '' union read = unionLimits read := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases mem_iUnion.mp hx with ⟨k, hx⟩
        rcases mem_iUnion.mp hx with ⟨hk, hx⟩
        exact mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, (hfixed k x).mp hx⟩⟩
      · intro hw
        rcases mem_iUnion.mp hw with ⟨k, hw⟩
        rcases mem_iUnion.mp hw with ⟨hk, hw⟩
        refine ⟨threadStream w, mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨hk, ?_⟩⟩, hthread w⟩
        apply (hfixed k _).mpr
        rwa [hthread]
    have htarget : limitUnions read = univ := by
      apply eq_univ_of_forall
      intro w n
      refine ⟨max 2 (n + 1), by omega, ?_⟩
      rw [hfull _ _ (by omega)]; trivial
    have hnotSurj : ¬ Function.Surjective (comparison read) := by
      intro hs
      have ht : prefixes (fun _ => true) ∈ limitUnions read := htarget.symm ▸ mem_univ _
      obtain ⟨w, hw⟩ := hs ⟨_, ht⟩
      have hp : w.val = prefixes (fun _ => true) := congrArg Subtype.val hw
      have hmem : prefixes (fun _ => true) ∈ unionLimits read := hp ▸ w.property
      rw [← hsource] at hmem
      obtain ⟨x, hx, heq⟩ := hmem
      have hx' := hinjective heq
      subst x
      rcases mem_iUnion.mp hx with ⟨k, hx⟩
      rcases mem_iUnion.mp hx with ⟨hk, hx⟩
      obtain ⟨i, hi⟩ := hx 0
      exact Bool.noConfusion hi

    have hhalf (b : Bool) : marginal fairBias {b} = (2 : ℝ≥0∞)⁻¹ := by
      cases b
      · rw [marginal, bernoulliMeasure_apply_of_notMem_of_mem fairBias
          (measurableSet_singleton _) (by simp) (by simp), ← ENNReal.coe_inv_two]
        apply congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞))
        apply Subtype.ext
        change 1 - (1 / 2 : ℝ) = (2 : ℝ)⁻¹
        norm_num
      · rw [marginal, bernoulliMeasure_apply_of_mem_of_notMem fairBias
          (measurableSet_singleton _) (by simp) (by simp), ← ENNReal.coe_inv_two]
        apply congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞))
        apply Subtype.ext
        change (1 / 2 : ℝ) = (2 : ℝ)⁻¹
        norm_num
    have haligned (k m : Nat) (hk : 2 ≤ k) :
        fairMeasure (aligned read k m) = (1 - (2 : ℝ≥0∞)⁻¹ ^ k) ^ m := by
      let f : Fin m × Fin k → Nat := fun p => p.1 * k + p.2
      have hf : Function.Injective f := by
        rintro ⟨r, i⟩ ⟨s, j⟩ heq
        have heq' : r.val * k + i.val = s.val * k + j.val := heq
        have hij : i.val = j.val := by
          have h := congrArg (fun n => n % k) heq'
          simpa [Nat.add_mod, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using h
        have hrs : r.val = s.val := by
          have hmul : r.val * k = s.val * k := by omega
          exact Nat.eq_of_mul_eq_mul_right (by omega) hmul
        exact Prod.ext (Fin.ext hrs) (Fin.ext hij)
      let blocks : Stream → Fin m → Word k := fun x r i => x (r * k + i)
      have hmap : fairMeasure.map blocks =
          Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin k => marginal fairBias)) := by
        have hflat := Measure.map_infinitePi_infinitePi_of_inj
          (P := fun _ : Nat => marginal fairBias) hf
        calc
          fairMeasure.map blocks =
              (fairMeasure.map (fun x p => x (f p))).map
                (MeasurableEquiv.curry (Fin m) (Fin k) Bool) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            rfl
          _ = Measure.infinitePi (fun _ : Fin m =>
              Measure.infinitePi (fun _ : Fin k => marginal fairBias)) := by
            rw [show fairMeasure.map (fun x p => x (f p)) =
              Measure.infinitePi (fun _ : Fin m × Fin k => marginal fairBias) from hflat]
            exact Measure.infinitePi_map_curry (fun (_ : Fin m) (_ : Fin k) => marginal fairBias)
          _ = _ := by simp_rw [Measure.infinitePi_eq_pi]
      let good : Set (Word k) := {fun _ => true}ᶜ
      have hgood : MeasurableSet good := (measurableSet_singleton _).compl
      have hgoodmass : Measure.pi (fun _ : Fin k => marginal fairBias) good =
          1 - (2 : ℝ≥0∞)⁻¹ ^ k := by
        rw [measure_compl (measurableSet_singleton _) (measure_ne_top _ _),
          measure_univ, Measure.pi_singleton]
        simp only [hhalf, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hevent : aligned read k m = blocks ⁻¹' (univ.pi (fun _ : Fin m => good)) := by
        ext x
        simp only [aligned, mem_ofPred_eq, mem_preimage, Set.mem_pi, mem_univ, true_implies]
        apply forall_congr'
        intro r
        simp only [good, mem_compl_iff, mem_singleton_iff, funext_iff, not_forall]
        apply exists_congr
        intro i
        change x (r * k + i) = false ↔ ¬x (r * k + i) = true
        cases x (r * k + i) <;> decide
      rw [hevent, ← Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi fun _ => hgood),
        hmap, Measure.pi_pi]
      simp only [hgoodmass, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hsubset (k m : Nat) : bounded read k ⊆ aligned read k m :=
      fun _ hx r => hx (r * k)
    have hnull (k : Nat) (hk : 2 ≤ k) : fairMeasure (bounded read k) = 0 := by
      apply le_antisymm _ bot_le
      have hlt : 1 - (2 : ℝ≥0∞)⁻¹ ^ k < 1 :=
        ENNReal.sub_lt_self (by simp) (by simp) (pow_ne_zero _ (by norm_num))
      apply ge_of_tendsto (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt)
      exact Eventually.of_forall fun m => (measure_mono (hsubset k m)).trans_eq (haligned k m hk)
    have hunull : fairMeasure (union read) = 0 :=
      measure_iUnion_null fun k => measure_iUnion_null fun hk => hnull k hk
    refine ⟨(fun k hk => ⟨hclosed k, hstrict k hk⟩),
      (fun k hk n => himage k (by omega) n), hfull, ?_, ?_,
      hunonempty, hdense, hproper, hmeas, huimage, hdense.closure_eq,
      hnull, hunull, ?_, ⟨hinjective, fun w => ⟨threadStream w, hthread w⟩⟩, ?_, ?_,
      hthread, hfixed, hsource, htarget, ?_, hnotSurj, (fun _ => rfl), ?_, ?_,
      (fun k m hk => ⟨hsubset k m, haligned k m hk⟩)⟩
    · intro k n w hw j hj
      obtain ⟨i, hi⟩ := hw j (by omega)
      exact ⟨⟨i, by omega⟩, hi⟩
    · rintro k m n h _ ⟨w, hw, rfl⟩ j hj
      obtain ⟨i, hi⟩ := hw j (hj.trans h)
      exact ⟨i, hi⟩
    · rw [hdense.closure_eq, measure_univ]
    · exact (continuous_pi fun n => continuous_pi fun i : Fin n => continuous_apply i.val).subtype_mk _
    · change Continuous (fun w : Threads => fun j : Nat => w.val (j + 1) ⟨j, by omega⟩)
      apply continuous_pi
      intro j
      exact (continuous_apply (⟨j, by omega⟩ : Fin (j + 1))).comp
        ((continuous_apply (j + 1)).comp continuous_subtype_val)
    · intro x y h
      apply Subtype.ext
      exact congrArg (fun z : limitUnions read => z.val) h
    · ext x
      simp only [union, mem_iUnion, mem_ofPred_eq, exists_prop]
      exact exists_congr fun k => and_congr_right fun _ => hfixed k x
    · apply eq_univ_of_forall
      intro x n
      refine ⟨max 2 (n + 1), by omega, ?_⟩
      rw [hfull _ _ (by omega)]; trivial

private theorem bitVariation : LeanInformationAudit.FiniteLawVariation bitArena := by
  refine ⟨bitRealization, cutRealization (fun _ : Bool => false), boundaryUnit.proof, ?_⟩
  intro h
  have hstrict := (h.1 2 (by omega)).2
  have heq : bounded (fun _ : Bool => false) 2 = bounded (fun _ : Bool => false) 3 := by
    ext x
    simp [bounded]
  exact hstrict.ne heq

private theorem bitSensitivity : LeanInformationAudit.FiniteSlotSensitivity bitArena := by
  obtain ⟨good, erased, hgood, herased⟩ := bitVariation
  constructor
  · intro i
    refine ⟨good, erased, ?_, ?_, ⟨fun _ => herased, fun _ => hgood⟩⟩
    · intro j hji
      cases i
      cases j
      exact (hji rfl).elim
    · intro j
      exact Fin.elim0 j
  · intro i
    exact Fin.elim0 i

local instance : DecidableEq bitArena.State := instDecidableEqBool

information_theorem bounded_run_union_boundary in bitArena
  readout via (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))
  primitives (@cutRealization Bool Bool instDecidableEqBool (fun b : Bool => b))
  variation bitVariation sensitivity bitSensitivity
  escape from (Bool) escape continues (open)
  : Boundary (fun b : Bool => b) := boundaryUnit.proof

#print axioms bounded_run_union_boundary
#print axioms bitVariation
#print axioms bitSensitivity

end D5.S3.ConceptDynamics.ExperimentBoundary.BoundedRunUnion
