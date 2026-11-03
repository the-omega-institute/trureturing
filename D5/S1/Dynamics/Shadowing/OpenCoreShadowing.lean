/- GID: D5/S1/Dynamics/Shadowing/OpenCoreShadowing
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/OpenCoreShadowing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Open pullbacks and an open core give a compact one-step extension with forward shadowing. -/

import D5.S1.Dynamics.Shadowing.GenericBinarySection
import D5.S1.Dynamics.Shadowing.MetricTracing
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.ShrinkingLemma
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.OfCompactT2

/-! Open pullbacks, the binary full shift, and shadowing for an open one-step
extension of a compact shadowing core. -/

open TopologicalSpace Set Function Filter UniformSpace
open scoped Topology Uniformity SetRel

namespace D5.S1.Dynamics.Shadowing.FreeFibreBoundary

noncomputable section
universe u v w

open scoped OnePoint

abbrev FibrePullback {T S B : Type*} (p : T → B) (rho : S → B) :=
  {z : T × S // p z.1 = rho z.2}

def fibrePullbackSecond {T S B : Type*} (p : T → B) (rho : S → B) :
    FibrePullback p rho → S := fun z => z.val.2

theorem fibrePullbackSecond_continuous {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B]
    (p : T → B) (rho : S → B) :
    Continuous (fibrePullbackSecond p rho) := by
  exact continuous_snd.comp continuous_subtype_val

theorem fibrePullbackSecond_isOpenMap {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B]
    (p : T → B) (rho : S → B) (hp : IsOpenMap p) (hrho : Continuous rho) :
    IsOpenMap (fibrePullbackSecond p rho) := by
  apply IsOpenMap.of_nhds_le
  intro z
  apply le_map_iff.2
  intro N hN
  obtain ⟨u, hu, hsub⟩ :=
    (mem_nhds_subtype ({z : T × S | p z.1 = rho z.2}) z N).mp hN
  obtain ⟨A, hA, C, hC, hAC⟩ := mem_nhds_prod_iff.mp hu
  have hpa : p '' A ∈ 𝓝 (p z.val.1) := hp.image_mem_nhds hA
  have hpa' : p '' A ∈ 𝓝 (rho z.val.2) := by
    rw [← z.property]
    exact hpa
  have hpre : rho ⁻¹' (p '' A) ∈ 𝓝 z.val.2 :=
    hrho.continuousAt.preimage_mem_nhds hpa'
  apply Filter.mem_of_superset (inter_mem hC hpre)
  intro s hs
  rcases hs.2 with ⟨t, htA, hpt⟩
  let z' : FibrePullback p rho := ⟨(t, s), hpt⟩
  refine ⟨z', ?_, rfl⟩
  apply hsub
  exact hAC ⟨htA, hs.1⟩

theorem fibrePullback_isClosed {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B] [T2Space B]
    (p : T → B) (rho : S → B) (hp : Continuous p) (hrho : Continuous rho) :
    IsClosed {z : T × S | p z.1 = rho z.2} := by
  exact isClosed_eq (hp.comp continuous_fst) (hrho.comp continuous_snd)

theorem fibrePullback_compactSpace {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B] [T2Space B]
    [CompactSpace T] [CompactSpace S]
    (p : T → B) (rho : S → B) (hp : Continuous p) (hrho : Continuous rho) :
    CompactSpace (FibrePullback p rho) := by
  exact (fibrePullback_isClosed p rho hp hrho).isClosedEmbedding_subtypeVal.compactSpace

theorem fibrePullback_t2Space {T S B : Type*}
    [TopologicalSpace T] [TopologicalSpace S] [TopologicalSpace B]
    [T2Space B] [T2Space T] [T2Space S]
    (p : T → B) (rho : S → B) : T2Space (FibrePullback p rho) := by
  infer_instance

abbrev CoreShift : BinaryName → BinaryName :=
  SymbolicDynamics.FullShift.shift (1 : ℕ)

abbrev FreeFibreSource {T : Type*} (p : T → OnePoint ℕ) (a : BinaryName) :=
  FibrePullback p (firstDifference a) ⊕ BinaryName

def sourceDynamics {T : Type*} (p : T → OnePoint ℕ) (a : BinaryName)
    (z : FibrePullback p (firstDifference a) ⊕ BinaryName) :
    FibrePullback p (firstDifference a) ⊕ BinaryName :=
  Sum.elim (fun z => Sum.inr z.val.2) (fun s => Sum.inr (CoreShift s)) z

def sourceObservation {T : Type*} (p : T → OnePoint ℕ) (a : BinaryName)
    (z : FibrePullback p (firstDifference a) ⊕ BinaryName) : BinaryName :=
  Sum.elim (fun z => z.val.2) CoreShift z

theorem sourceDynamics_continuous {T : Type*} [TopologicalSpace T]
    (p : T → OnePoint ℕ) (a : BinaryName) :
    Continuous (sourceDynamics p a) := by
  exact (continuous_inr.comp (continuous_snd.comp continuous_subtype_val)).sumElim
    (continuous_inr.comp (SymbolicDynamics.FullShift.continuous_shift 1))

theorem sourceObservation_continuous {T : Type*} [TopologicalSpace T]
    (p : T → OnePoint ℕ) (a : BinaryName)
    (hH : Continuous (fibrePullbackSecond p (firstDifference a))) :
    Continuous (sourceObservation p a) := by
  exact hH.sumElim (SymbolicDynamics.FullShift.continuous_shift 1)

theorem sourceDynamics_semiconj {T : Type*} (p : T → OnePoint ℕ) (a : BinaryName) :
    Semiconj (sourceObservation p a) (sourceDynamics p a) CoreShift := by
  intro z
  cases z <;> rfl

def boolPrefixRel (k : ℕ) : SetRel BinaryName BinaryName :=
  {p | ∀ i < k, p.1 i = p.2 i}

theorem boolPrefixRel_mem (k : ℕ) : boolPrefixRel k ∈ 𝓤 BinaryName := by
  have hi (i : Fin k) : {p : BinaryName × BinaryName | p.1 i.val = p.2 i.val} ∈
      𝓤 BinaryName := by
    simpa only [Filter.mem_map, SetRel.id, Prod.map, Set.mem_ofPred_eq,
      Set.preimage_ofPred_eq] using
      (Pi.uniformContinuous_proj (fun _ : ℕ => Bool) i.val)
        (DiscreteUniformity.relId_mem_uniformity Bool)
  have h : (⋂ i : Fin k, {p : BinaryName × BinaryName | p.1 i.val = p.2 i.val}) ∈
      𝓤 BinaryName := Filter.iInter_mem.mpr hi
  apply Filter.mem_of_superset h
  intro p hp i hi
  exact Set.mem_iInter.mp hp ⟨i, hi⟩

theorem boolPrefixRel_cofinal (U : SetRel BinaryName BinaryName)
    (hU : U ∈ 𝓤 BinaryName) :
    ∃ k : ℕ, 0 < k ∧ boolPrefixRel k ⊆ U := by
  letI : MetricSpace BinaryName := PiNat.metricSpaceOfDiscreteUniformity
    (fun _ : ℕ => DiscreteUniformity.eq_principal_setRelId Bool)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨k + 1, by omega, ?_⟩
  intro p hp
  apply hεU
  have hdist : dist p.1 p.2 ≤ (1 / 2 : ℝ) ^ k :=
    PiNat.mem_cylinder_iff_dist_le.mp
      (show p.1 ∈ PiNat.cylinder p.2 k from fun i hi => hp i (by omega))
  exact hdist.trans_lt hk

theorem coreShift_uniformHasShadowing : UniformHasShadowing CoreShift := by
  intro E hE
  obtain ⟨k, hk, hEk⟩ := boolPrefixRel_cofinal E hE
  let D := boolPrefixRel (k + 1)
  have hD : D ∈ 𝓤 BinaryName := boolPrefixRel_mem (k + 1)
  refine ⟨D, hD, ?_⟩
  intro z hz
  refine ⟨diagonalSplice z, ?_⟩
  intro i
  apply hEk
  intro j hj
  change CoreShift^[i] (diagonalSplice z) j = z i j
  rw [shift_one_iterate_apply]
  exact diagonal_splice_overlap z k (fun n l hl => by
    have hn := hz n
    change (CoreShift (z n), z (n + 1)) ∈ boolPrefixRel (k + 1) at hn
    have hnl := hn l (by simpa [boolPrefixRel] using hl)
    simpa [CoreShift, SymbolicDynamics.FullShift.shift_apply, Nat.add_comm] using hnl) i j
    (by omega)

def prependBinaryName (b : Bool) (s : BinaryName) : BinaryName :=
  fun n => if n = 0 then b else s (n - 1)

theorem prependBinaryName_shift (b : Bool) (s : BinaryName) :
    CoreShift (prependBinaryName b s) = s := by
  funext n
  simp [CoreShift, prependBinaryName, SymbolicDynamics.FullShift.shift_apply]

theorem coreShift_isOpenMap : IsOpenMap CoreShift := by
  refine (isTopologicalBasis_pi (fun _ => isTopologicalBasis_opens)).isOpenMap_iff.2 ?_
  rintro _ ⟨U, F, hUF, rfl⟩
  apply isOpen_pi_iff.mpr
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  let I : Finset ℕ := F.filter (fun n => 0 < n) |>.image (fun n => n - 1)
  let W : ℕ → Set Bool := fun j =>
    if j + 1 ∈ F then U (j + 1) else Set.univ
  refine ⟨I, W, ?_, ?_⟩
  · intro j hj
    have hj' : ∃ n ∈ F, 0 < n ∧ n - 1 = j := by
      rcases Finset.mem_image.mp hj with ⟨n, hn, rfl⟩
      exact ⟨n, (Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2, rfl⟩
    obtain ⟨n, hnF, hnpos, hnj⟩ := hj'
    subst j
    have hnmem : n ∈ F := hnF
    have hopen : IsOpen (U n) := hUF n hnmem
    have hmem : x n ∈ U n := Set.mem_pi.mp hx n hnF
    have hW : W (n - 1) = U n := by
      dsimp [W]
      rw [show n - 1 + 1 = n by omega, if_pos hnF]
    have hshiftmem : (CoreShift x) (n - 1) ∈ U n := by
      have hidx : 1 + (n - 1) = n := by omega
      simpa [CoreShift, SymbolicDynamics.FullShift.shift_apply, hidx] using hmem
    simpa [hW, hshiftmem]
  · intro s hs
    let x' := prependBinaryName (x 0) s
    have hx' : x' ∈ (F : Set ℕ).pi U := by
      apply Set.mem_pi.mpr
      intro n hnF
      by_cases hn0 : n = 0
      · subst n
        simpa [x', prependBinaryName] using Set.mem_pi.mp hx 0 hnF
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hj : n - 1 ∈ I := by
          apply Finset.mem_image.mpr
          exact ⟨n, Finset.mem_filter.mpr ⟨hnF, hnpos⟩, rfl⟩
        have hsW := Set.mem_pi.mp hs (n - 1) hj
        have hW : W (n - 1) = U n := by
          dsimp [W]
          have hnF' : n ∈ F := hnF
          simp [show n - 1 + 1 = n by omega, hnF']
        have hsU : s (n - 1) ∈ U n := by simpa [hW] using hsW
        simpa [x', prependBinaryName, hn0] using hsU
    refine ⟨x', hx', ?_⟩
    exact prependBinaryName_shift (x 0) s

theorem open_core_extension_hasShadowing
    {P S : Type*} [UniformSpace P] [UniformSpace S] [CompactSpace P] [CompactSpace S]
    [T2Space P] [T2Space S]
    (h : P ⊕ S → S) (g : S → S)
    (hcont : Continuous h) (hopen : IsOpenMap h) (honto : Function.Surjective h)
    (hcore : ∀ s, h (Sum.inr s) = g s) (hgcont : Continuous g)
    (hgs : HasShadowing g) :
    HasShadowing (fun x : P ⊕ S => Sum.inr (h x)) := by
  let F : P ⊕ S → P ⊕ S := fun x => Sum.inr (h x)
  have hF : Continuous F := continuous_inr.comp hcont
  have hgu : UniformHasShadowing g := (cover_shadowing_iff_uniform g).mp hgs
  apply (cover_shadowing_iff_uniform F).mpr
  intro E hE
  obtain ⟨V, hV, hVo, hVs, hVcomp⟩ := comp_open_symm_mem_uniformity_sets hE
  obtain ⟨C, hC⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (P ⊕ S))).elim_finite_subcover
      (fun x => UniformSpace.ball x V)
      (fun x => UniformSpace.isOpen_ball _ hVo)
      (by
        intro x _
        exact Set.mem_iUnion.mpr ⟨x, mem_ball_self x hV⟩)
  let ι := C
  let Uι : ι → Set (P ⊕ S) := fun i => UniformSpace.ball (i : P ⊕ S) V
  have hUι : ∀ i, IsOpen (Uι i) := fun i => UniformSpace.isOpen_ball _ hVo
  have hUcover : (Set.univ : Set (P ⊕ S)) ⊆ ⋃ i : ι, Uι i := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hC hx)
    exact Set.mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
  obtain ⟨v, hvcover, hvopen, hvcl, hvcompact⟩ :=
    exists_subset_iUnion_closure_subset_t2space (s := (Set.univ : Set (P ⊕ S)))
      isCompact_univ hUι (fun x _ => Set.toFinite _) hUcover
  let Ki : ι → Set S := fun i => h '' closure (v i)
  have hKi : ∀ i, IsCompact (Ki i) := fun i => (hvcompact i).image hcont
  have hKiU : ∀ i, Ki i ⊆ h '' Uι i := by
    intro i y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hvcl i hx, rfl⟩
  have hUi : ∀ i, IsOpen (h '' Uι i) := fun i => hopen _ (hUι i)
  have hRexist : ∀ i, ∃ R : SetRel S S, R ∈ 𝓤 S ∧ IsOpen R ∧
      ∀ x ∈ Ki i, UniformSpace.ball x R ⊆ h '' Uι i := fun i =>
    lebesgue_number_of_compact_open (hKi i) (hUi i) (hKiU i)
  choose Ri hRi hRopen hRball using hRexist
  let L : SetRel S S := ⋂ i : ι, Ri i
  have hL : L ∈ 𝓤 S := Filter.iInter_mem.mpr (fun i => hRi i)
  have hLift : ∀ x : P ⊕ S, ∀ b : S, (h x, b) ∈ L →
      ∃ y : P ⊕ S, h y = b ∧ (y, x) ∈ E := by
    intro x b hxb
    obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hvcover (Set.mem_univ x))
    have hxs : x ∈ closure (v i) := subset_closure hxi
    have hhb : b ∈ UniformSpace.ball (h x) (Ri i) :=
      Set.mem_iInter.mp hxb i
    have hhb' : b ∈ h '' Uι i := hRball i (h x) ⟨x, hxs, rfl⟩ hhb
    rcases hhb' with ⟨y, hy, hhy⟩
    have hxiU : x ∈ Uι i := hvcl i hxs
    have hye : (y, x) ∈ V ○ V :=
      mem_comp_of_mem_ball (V := V) (W := V) (x := y) (y := x) (z := (i : P ⊕ S))
        (show y ∈ UniformSpace.ball (i : P ⊕ S) V from hy)
        (show x ∈ UniformSpace.ball (i : P ⊕ S) V from hxiU)
    exact ⟨y, hhy, hVcomp hye⟩
  obtain ⟨R, hR, hRo, hRs, hRcomp⟩ :=
    comp_open_symm_mem_uniformity_sets (inter_mem hL
      ((uniformContinuous_inr : UniformContinuous (Sum.inr : S → P ⊕ S)) hE))
  let Dcore : SetRel S S := Classical.choose (hgu R hR)
  have hDcore : Dcore ∈ 𝓤 S := (Classical.choose_spec (hgu R hR)).1
  have htrace_spec := (Classical.choose_spec (hgu R hR)).2
  let Q : SetRel S S := R ∩ (fun z : S × S => (g z.1, g z.2)) ⁻¹' Dcore
  have hQg : Q ∈ 𝓤 S := inter_mem hR ((CompactSpace.uniformContinuous_of_continuous hgcont) hDcore)
  let D : SetRel (P ⊕ S) (P ⊕ S) :=
    Prod.map Sum.inl Sum.inl '' (Set.univ : SetRel P P) ∪
      Prod.map Sum.inr Sum.inr '' Q
  have hD : D ∈ 𝓤 (P ⊕ S) := union_mem_uniformity_sum univ_mem hQg
  refine ⟨D, hD, ?_⟩
  intro z hz
  have hnext : ∀ n, ∃ s : S, z (n + 1) = Sum.inr s ∧ (h (z n), s) ∈ Q := by
    intro n
    have hn : (F (z n), z (n + 1)) ∈ D := by simpa [F, D] using hz n
    cases hz1 : z (n + 1) with
    | inl p => simp [D, F, hz1] at hn
    | inr s =>
      refine ⟨s, rfl, ?_⟩
      simpa [D, F, hz1] using hn
  have hcorepseudo : UniformPseudoOrbit g Dcore (fun n => h (z n)) := by
    intro n
    obtain ⟨s, hs, hqs⟩ := hnext n
    have hpre := hqs.2
    have hstep : (g (h (z n)), g s) ∈ Dcore := hpre
    simpa [hs, hcore] using hstep
  obtain ⟨b, hb⟩ := htrace_spec (fun n => h (z n)) hcorepseudo
  have hRb : (h (z 0), b) ∈ R := by
    have hb0 := hb 0
    letI : SetRel.IsSymm R := hRs
    have h' : h (z 0) ∈ UniformSpace.ball (b) R := by
      change (b, h (z 0)) ∈ R
      exact hb0
    have h'' := (mem_ball_symmetry).mp h'
    change (h (z 0), b) ∈ R at h''
    exact h''
  obtain ⟨y, hyb, hyE⟩ := hLift (z 0) b ((hRcomp (mem_comp_of_mem_ball
    (V := R) (W := R) (mem_ball_self _ hR) hRb)).1)
  refine ⟨y, ?_⟩
  have hyiter : ∀ n : ℕ, F^[n + 1] y = Sum.inr (g^[n] b) := by
    intro n
    induction n with
    | zero => simpa [F, hyb]
    | succ n ih =>
      rw [show n + 1 + 1 = 1 + (n + 1) by omega, iterate_add_apply]
      simp [F, ih, hcore]
      exact (iterate_succ_apply' g n b).symm.trans (iterate_succ_apply g n b)
  intro n
  cases n with
  | zero => simpa [F] using hyE
  | succ n =>
    obtain ⟨s, hs, hqs⟩ := hnext n
    have hcomp : (g^[n] b, s) ∈ R ○ R :=
      ⟨h (z n), hb n, hqs.1⟩
    have hEcore := (hRcomp hcomp).2
    simpa [hyiter, hs] using hEcore

end
end D5.S1.Dynamics.Shadowing.FreeFibreBoundary
