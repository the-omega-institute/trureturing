/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion
   generality: G
   anchors: []
   utility: none
   digest: Actual source completions retain exact family margins and full-storage conclusions. -/

import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.EReal.Basic
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.StrictSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.ClosedSupply
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Bilateral
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Completion
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.CanonicalGeometry

set_option maxHeartbeats 4000000 in
-- Actual record construction and finite liveness share the full decoder recurrence.
/-- Complete readable configurations evolve without reading the append-only output.
Safety and positionwise liveness on actual records separate the original paired
family at the unobserved-terminal departure cut. The actual first stem difference
is zero, so the joint prefix factor is one and configuration separation follows. -/
theorem actual_decoder_configuration_extraction
    {Configuration : Type*}
    (advance : Configuration → Color → Configuration × List Label)
    (initialConfiguration : Configuration) (initialOutput : List Label)
    (model : Model) (o : Ownership) (b : ℝ) (contract : Contract)
    (N : ℕ) (family : Finset (List Return))
    (weight : ∀ xs ∈ family, listWeight xs = N)
    (supply : ∀ xs ∈ family, ActualPairSupply model o b contract xs) :
    let evolve := fun (v : Configuration × List Label) (c : Color) =>
      let next := advance v.1 c
      (next.1, v.2 ++ next.2)
    let run := fun h : List Color => h.foldl evolve (initialConfiguration, initialOutput)
    let front := fun (r : ℕ → Color) (n : ℕ) => List.ofFn (fun p : Fin n => r p.val)
    let omega := fun (a : ℕ → Label) (x : ℕ → ℝ) =>
      ∃ path : ℕ → Guard, path 0 = .G0 ∧
        (∀ p, nextGuard (path p) (a p) = some (path (p + 1))) ∧
        (∀ p, InSupport (path p) (x p)) ∧
        (∀ p, x p = branch (a p) (x (p + 1)))
    let record := fun (a : ℕ → Label) (r : ℕ → Color) =>
      ∃ x : ℕ → ℝ, omega a x ∧ ∃ err : ℕ → ℝ,
        ErrorBound b contract err ∧ ∀ p, observe o (x p) (err p) = r p
    let finiteSource := fun a : ℕ → Label => ∃ M : ℕ, ∀ p, M ≤ p → a p = .L0
    let pairedRecord := fun (xs : List Return) (j : Side) (p : ℕ) =>
      if hp : p < (history model xs).length then (history model xs)[p]
      else observe o (coordinate (tailPrefix j) (p - (history model xs).length)) 0
    (∀ a r, record a r → ∀ n p (hp : p < (run (front r n)).2.length),
      (run (front r n)).2[p] = a p) →
    (∀ a r, record a r → finiteSource a → ∀ p, ∃ n, p < (run (front r n)).2.length) →
    letI := Classical.decEq Configuration
    (∀ xs ∈ family, ∀ j,
      record (source j model xs) (pairedRecord xs j) ∧ finiteSource (source j model xs)) ∧
    (∀ xs ∈ family, (run (history model xs)).2 = []) ∧
    Set.InjOn (fun xs => run (history model xs)) (family : Set (List Return)) ∧
    Set.InjOn (fun xs => (run (history model xs)).1) (family : Set (List Return)) ∧
    family.card ≤ (family.image (fun xs => (run (history model xs)).1)).card * (0 + 1) := by
  classical
  dsimp only
  let evolve := fun (v : Configuration × List Label) (c : Color) =>
    let next := advance v.1 c
    (next.1, v.2 ++ next.2)
  let run := fun h : List Color => h.foldl evolve (initialConfiguration, initialOutput)
  let front := fun (r : ℕ → Color) (n : ℕ) => List.ofFn (fun p : Fin n => r p.val)
  let omega := fun (a : ℕ → Label) (x : ℕ → ℝ) =>
    ∃ path : ℕ → Guard, path 0 = .G0 ∧
      (∀ p, nextGuard (path p) (a p) = some (path (p + 1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = branch (a p) (x (p + 1)))
  let record := fun (a : ℕ → Label) (r : ℕ → Color) =>
    ∃ x : ℕ → ℝ, omega a x ∧ ∃ err : ℕ → ℝ,
      ErrorBound b contract err ∧ ∀ p, observe o (x p) (err p) = r p
  let finiteSource := fun a : ℕ → Label => ∃ M : ℕ, ∀ p, M ≤ p → a p = .L0
  let pairedRecord := fun (xs : List Return) (j : Side) (p : ℕ) =>
    if hp : p < (history model xs).length then (history model xs)[p]
    else observe o (coordinate (tailPrefix j) (p - (history model xs).length)) 0
  change (∀ a r, record a r → ∀ n p (hp : p < (run (front r n)).2.length),
    (run (front r n)).2[p] = a p) →
    (∀ a r, record a r → finiteSource a → ∀ p, ∃ n, p < (run (front r n)).2.length) → _
  intro safety liveness
  have actual (xs : List Return) (hx : xs ∈ family) (j : Side) :
      record (source j model xs) (pairedRecord xs j) ∧ finiteSource (source j model xs) := by
    have reconstruction := paired_source_reconstruction j model xs
    obtain ⟨path, hzero, hedges, hsupport, haffine⟩ :=
      literal_address_path .G0 .G0 (sourcePrefix j model xs) reconstruction.1
    obtain ⟨err, hbound, hslots, hzeroErr, hfuture⟩ := supply xs hx j
    have lengths : (observedPrefix j model xs).length = (history model xs).length :=
      reconstruction.2.2.2.2.1.trans reconstruction.2.2.2.2.2.1.symm
    constructor
    · refine ⟨coordinate (sourcePrefix j model xs), ⟨path, hzero, hedges, hsupport, haffine⟩,
        err, hbound, ?_⟩
      intro p
      by_cases hp : p < (history model xs).length
      · simpa only [pairedRecord, dif_pos hp] using hslots p hp
      · have hge : (history model xs).length ≤ p := Nat.le_of_not_gt hp
        have he : (observedPrefix j model xs).length + (p - (history model xs).length) = p := by
          rw [lengths, Nat.add_sub_of_le hge]
        have hf := hfuture (p - (history model xs).length)
        rw [he] at hf
        simpa only [pairedRecord, dif_neg hp] using hf
    · refine ⟨(sourcePrefix j model xs).length, ?_⟩
      intro p hp
      simp only [source, address, List.getElem?_eq_none hp, Option.getD_none]
  have past (xs : List Return) (j : Side) :
      front (pairedRecord xs j) (history model xs).length = history model xs := by
    apply List.ext_getElem (by simp [front])
    intro p hp hq
    simp [front, pairedRecord, hq]
  have frontAdd (r : ℕ → Color) (n m : ℕ) :
      front r (n + m) = front r n ++ front (fun p => r (n + p)) m := by
    simp [front, List.ofFn_add]
  have splice (xs : List Return) (j : Side) (n : ℕ) :
      front (pairedRecord xs j) ((history model xs).length + n) =
        history model xs ++ front (fun p => observe o (coordinate (tailPrefix j) p) 0) n := by
    rw [frontAdd, past]
    have same : (fun p => pairedRecord xs j ((history model xs).length + p)) =
        (fun p => observe o (coordinate (tailPrefix j) p) 0) := by
      funext p
      have hn : ¬ (history model xs).length + p < (history model xs).length := by omega
      simp only [pairedRecord, dif_neg hn, Nat.add_sub_cancel_left]
    exact congrArg (fun r : ℕ → Color => history model xs ++ front r n) same
  have emittedEmpty (xs : List Return) (hx : xs ∈ family) :
      (run (history model xs)).2 = [] := by
    have hh := (actual xs hx .high).1
    have hl := (actual xs hx .low).1
    cases ho : (run (history model xs)).2 with
    | nil => rfl
    | cons l rest =>
      have hhpos : 0 < (run (front (pairedRecord xs .high) (history model xs).length)).2.length := by
        rw [past, ho]; simp
      have hlpos : 0 < (run (front (pairedRecord xs .low) (history model xs).length)).2.length := by
        rw [past, ho]; simp
      have hhigh := safety _ _ hh (history model xs).length 0 hhpos
      have hlow := safety _ _ hl (history model xs).length 0 hlpos
      have eh : l = Label.L5 := by
        simpa [past, ho, source, address, sourcePrefix, observedPrefix, stem, block, U] using hhigh
      have el : l = Label.L0 := by
        simpa [past, ho, source, address, sourcePrefix, observedPrefix, stem, block, V] using hlow
      cases eh.symm.trans el
  have outputGrows (v : Configuration × List Label) (h : List Color) :
      v.2.length ≤ (h.foldl evolve v).2.length := by
    induction h generalizing v with
    | nil => exact le_refl _
    | cons c h ih =>
      have one : v.2.length ≤ (evolve v c).2.length := by
        dsimp [evolve]
        simp only [List.length_append]
        exact Nat.le_add_right _ _
      exact one.trans (ih (evolve v c))
  have configurationInj : Set.InjOn (fun xs => (run (history model xs)).1)
      (family : Set (List Return)) := by
    intro xs hx ys hy heq
    have hx' : xs ∈ family := hx
    have hy' : ys ∈ family := hy
    have cutEq : run (history model xs) = run (history model ys) :=
      Prod.ext heq ((emittedEmpty xs hx').trans (emittedEmpty ys hy').symm)
    have commonFuture (n : ℕ) :
        run (front (pairedRecord xs .high) ((history model xs).length + n)) =
        run (front (pairedRecord ys .high) ((history model ys).length + n)) := by
      rw [splice, splice]
      dsimp only [run]
      rw [List.foldl_append, List.foldl_append]
      exact congrArg (fun v =>
        (front (fun p => observe o (coordinate (tailPrefix .high) p) 0) n).foldl evolve v) cutEq
    have actualX := actual xs hx' .high
    have actualY := actual ys hy' .high
    apply actual_source_address_injection .high model xs ys ((weight xs hx').trans (weight ys hy').symm)
    funext p
    obtain ⟨n, hposition⟩ := liveness _ _ actualX.1 actualX.2 p
    have hlong : p < (run (front (pairedRecord xs .high)
        ((history model xs).length + n))).2.length := by
      have hg : (run (front (pairedRecord xs .high) n)).2.length ≤
          (run (front (pairedRecord xs .high) (n + (history model xs).length))).2.length := by
        rw [frontAdd]
        dsimp only [run]
        rw [List.foldl_append]
        exact outputGrows _ _
      rw [Nat.add_comm] at hg
      exact hposition.trans_le hg
    have sameOutput := congrArg Prod.snd (commonFuture n)
    have hyposition : p < (run (front (pairedRecord ys .high)
        ((history model ys).length + n))).2.length := by
      rw [← sameOutput]; exact hlong
    calc
      source .high model xs p =
          (run (front (pairedRecord xs .high) ((history model xs).length + n))).2[p] :=
        (safety _ _ actualX.1 _ p hlong).symm
      _ = (run (front (pairedRecord ys .high) ((history model ys).length + n))).2[p] := by
        simp only [sameOutput]
      _ = source .high model ys p := safety _ _ actualY.1 _ p hyposition
  refine ⟨actual, emittedEmpty, ?_, configurationInj, ?_⟩
  · intro xs hx ys hy hpair
    exact configurationInj hx hy (congrArg Prod.fst hpair)
  · rw [Finset.card_image_of_injOn configurationInj]
    simp


open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Filter
open scoped Topology

set_option maxHeartbeats 2000000 in
/-- Full actual-source peak storage has the necessary lower-limit coefficient
of the original weak-list rate. Fixed-codebook bounds are taken before the
codebook weight tends to infinity; no common margin across weights is used. -/
theorem original_complete_storage_liminf {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (b : ℝ) (contract : Contract) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K * (aSide .high / (1 - rho * chi ^ K)))
    (safety : ∀ a r, OperationRecord o b contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o b contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ a r, OperationRecord o b contract a r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
        (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o b contract) H c}) :
    ∀ sourceModel : Model,
    let W (n : ℕ) := Nat.card {xs : List Return //
      GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
      listWeight xs=n}
    ENNReal.ofReal (limsup (fun n : ℕ =>
      Real.logb 2 ((max 1 (W n) : ℕ) : ℝ)/(n : ℝ)) atTop) ≤
      liminf (fun H : ℕ => ENat.toENNReal
        (Peak action initialConfiguration (OperationRecord o b contract) encoding H)/
        (H : ENNReal)) atTop := by
  classical
  obtain ⟨R,hr,codebooks⟩ := original_codebook_storage_liminf action initialConfiguration
    o b contract K hK hqb hbp safety liveness postprocessing encoding faithful
  intro sourceModel
  dsimp only
  let W (n : ℕ) := Nat.card {xs : List Return //
    GuardTrace K ((lam-b)/g^2/chi^K) false .high xs (initial .high sourceModel) ∧
    listWeight xs=n}
  let r (n : ℕ) := Real.logb 2 ((max 1 (W n) : ℕ) : ℝ)/(n : ℝ)
  let C_R := 20+6*R.m
  let s (n : ℕ) := Real.logb 2 ((max 1 (W n) : ℕ) : ℝ)/((n+C_R : ℕ) : ℝ)
  let c := liminf (fun H : ℕ => ENat.toENNReal
    (Peak action initialConfiguration (OperationRecord o b contract) encoding H)/(H : ENNReal)) atTop
  change ENNReal.ofReal (limsup r atTop) ≤ c
  by_cases hc : c=⊤
  · rw [hc]; exact le_top
  have common (n : ℕ) (hn : 0<n) : ENNReal.ofReal (s n) ≤ c := by
    by_cases ha : 1≤W n
    · simpa only [W,C_R,s,max_eq_right ha] using (codebooks sourceModel n hn ha .original).2
    · have hz : W n=0 := by omega
      simp [s,hz]
  have logpos (n : ℕ) : 0 ≤ Real.logb 2 ((max 1 (W n) : ℕ) : ℝ) :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (Nat.le_max_left 1 (W n)))
  have rpos (n : ℕ) : 0≤r n := div_nonneg (logpos n) (by positivity)
  have crpos : 0≤c.toReal := ENNReal.toReal_nonneg
  have rb : IsBoundedUnder (· ≤ ·) atTop r := by
    apply isBoundedUnder_of_eventually_le (a := c.toReal*(1+(C_R : ℝ)))
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have np : (0 : ℝ)<(n : ℝ) := by exact_mod_cast hn
    have n1 : (1 : ℝ)≤(n : ℝ) := by exact_mod_cast hn
    have ncp : (0 : ℝ)<((n+C_R : ℕ) : ℝ) := by exact_mod_cast (show 0<n+C_R by omega)
    have cp : 0≤(C_R : ℝ) := by positivity
    have h := (ENNReal.ofReal_le_iff_le_toReal hc).mp (common n hn)
    dsimp [s] at h
    rw [div_le_iff₀ ncp] at h
    push_cast at h
    dsimp [r]
    rw [div_le_iff₀ np]
    have gain := mul_nonneg (mul_nonneg crpos cp) (sub_nonneg.mpr n1)
    push_cast
    nlinarith only [h,gain]
  let v (n : ℕ) : ℝ := (n : ℝ)/((n+C_R : ℕ) : ℝ)
  have vp : ∀ᶠ n in atTop, 0≤v n := Eventually.of_forall fun n => by dsimp [v]; positivity
  have vb : IsBoundedUnder (· ≤ ·) atTop v := by
    apply isBoundedUnder_of_eventually_le (a := (1 : ℝ))
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have np : (0 : ℝ)<((n+C_R : ℕ) : ℝ) := by exact_mod_cast (show 0<n+C_R by omega)
    dsimp [v]
    rw [div_le_iff₀ np,one_mul]
    exact_mod_cast Nat.le_add_right n C_R
  have vt : Tendsto v atTop (𝓝 1) := by
    simpa only [v,Nat.cast_add] using tendsto_natCast_div_add_atTop (C_R : ℝ)
  have products : (r*v) =ᶠ[atTop] s := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have np : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
    dsimp [r,v,s]
    field_simp
  have prodNonneg : ∃ᶠ n in atTop, 0≤(r*v) n :=
    (Frequently.of_forall rpos).and_eventually vp |>.mono (fun n h => mul_nonneg h.1 h.2)
  have prodBound : ∀ᶠ n in atTop, (r*v) n ≤ c.toReal := by
    filter_upwards [eventually_gt_atTop (0 : ℕ),products] with n hn he
    rw [he]
    exact (ENNReal.ofReal_le_iff_le_toReal hc).mp (common n hn)
  have upper : limsup (r*v) atTop ≤ c.toReal :=
    limsup_le_of_le (IsCoboundedUnder.of_frequently_ge prodNonneg) prodBound
  have lower := le_limsup_mul (Frequently.of_forall rpos) rb vp vb
  rw [vt.liminf_eq,mul_one] at lower
  have result := ENNReal.ofReal_le_ofReal (lower.trans upper)
  simpa only [ENNReal.ofReal_toReal hc] using result


set_option maxHeartbeats 1000000
open Filter Topology

theorem canonical_high_fixed_finite_tail
    (o : Ownership) (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (U i).length = L)
    (hVlen : ∀ i, (V i).length = L)
    (hlegal : ∀ i, LegalWord s1 s1 (U i)) (hV : ∀ i, LegalWord s2 s2 (V i))
    (hdifferent : U false ≠ U true) (hcolors : ∀ i, (U i).length = (W i).length) :
    let θ := familyEndpointBudget P Q h U V W L
    0 ≤ θ ∧ (familyEndpointCosts P Q h U V W L).length = 2*h.length+4*L ∧
    EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) Q h ∧
    (∀ i, EndpointCertificate θ (canonicalReturnLo V L) (canonicalReturnHi V L) (V i) (W i)) ∧
    ∃ (e : Guard) (w : List Label), LegalWord s1 e w ∧
      canonicalReturnLo U L < coordinate w 0 ∧ coordinate w 0 < canonicalReturnHi U L ∧
      ∀ zs : List Bool,
        OperationRecord o θ .closed (address ((P ++ choiceBlocks U zs) ++ w))
          (recordWithTail o (h ++ choiceBlocks W zs) w) ∧
        OperationFiniteSource (address ((P ++ choiceBlocks U zs) ++ w)) ∧
        ∀ p, recordWithTail o (h ++ choiceBlocks W zs) w
          ((h ++ choiceBlocks W zs).length+p) = observe o (coordinate w p) 0 := by
  let θ := familyEndpointBudget P Q h U V W L
  obtain ⟨hθ,count,highStem,highReturns,lowStem,lowReturns⟩ :=
    family_endpoint_certificates o s1 s2 P Q h hP hQ hPlen hQlen U V W L hL
      hlen hVlen hlegal hV hcolors
  have highHull := canonical_legal_return_hull s1 U L hL hlen hlegal
  refine ⟨hθ,count,lowStem,lowReturns,?_⟩
  exact fixed_finite_tail_all_histories o θ hθ s1 P h hP hPlen U W hlegal hcolors
    (canonicalReturnLo U L) (canonicalReturnHi U L) (highHull.2.1 hdifferent)
    highHull.2.2.1 highHull.2.2.2.1 highStem highReturns

/-- The actual canonical high hull and a canonical competing singleton supply
all synchronized sources and the arbitrary common-stem count. Geometry and the
identical competing word are derived from the legal families. The finite endpoint
budget derives the high certificates; the exact owned-endpoint orbit criterion
remains an explicit original feasibility condition. -/
theorem canonical_synchronous_common_stem {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (θ : ℝ)
    (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L) (hU : ∀ i, LegalWord s1 s1 (U i))
    (hV : ∀ i, LegalWord s2 s2 (V i)) (hUlen : ∀ i, (U i).length = L)
    (hVlen : ∀ i, (V i).length = L) (hUWlen : ∀ i, (U i).length = (W i).length)
    (differentReturns : U false ≠ U true)
    (hbudget : familyEndpointBudget P Q h U V W L ≤ θ)
    (competingSingleton : canonicalReturnLo V L = canonicalReturnHi V L)
    (hfeasible : if 0 < (-g)^L then
      (CompetingT o θ s2 Q (V false) h W).Nonempty ∧
        canonicalReturnLo V L ∈ closure (CompetingT o θ s2 Q (V false) h W)
      else canonicalReturnLo V L ∈ CompetingT o θ s2 Q (V false) h W)
    (k : ℕ) (hk : k < P.length)
    (sameStem : ∀ p (hp : p < k), P[p] = Q[p]'(by omega))
    (differentStem : P[k] ≠ Q[k]'(by omega))
    (safety : ∀ alpha r, OperationRecord o θ .closed alpha r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = alpha p)
    (liveness : ∀ alpha r, OperationRecord o θ .closed alpha r → OperationFiniteSource alpha → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ alpha r, OperationRecord o θ .closed alpha r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
      (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t) :
    ∃ (e : Guard) (w : List Label) (eta : ℕ → Label) (x : ℕ → ℝ),
      LegalWord s1 e w ∧ (canonicalReturnLo U L) < coordinate w 0 ∧ coordinate w 0 < (canonicalReturnHi U L) ∧
      ∀ n : ℕ, ∃ (beta : (Fin n → Bool) → ℕ → Label)
        (cuts : (Fin n → Bool) → Frame Configuration Label) (states : Finset Configuration),
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed
          (address (synchronousPrefix P U z ++ w))
          (recordWithTail o (synchronousPrefix h W z) w) ∧
          OperationFiniteSource (address (synchronousPrefix P U z ++ w))) ∧
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed (beta z)
          (recordWithOmegaTail o (synchronousPrefix h W z) x)) ∧
        (∀ (z : Fin n → Bool) p (hp : p < (synchronousPrefix Q V z).length),
          beta z p = (synchronousPrefix Q V z)[p]) ∧
        (∀ (z : Fin n → Bool) p, beta z (P.length+n*L+p) = eta p) ∧
        (∀ (z : Fin n → Bool) p, recordWithTail o (synchronousPrefix h W z) w (P.length+n*L+p) =
          observe o (coordinate w p) 0) ∧
        Function.Injective (fun z : Fin n → Bool => address (synchronousPrefix P U z ++ w)) ∧
        (∀ (z : Fin n → Bool), Cut action initialConfiguration
          (front (recordWithTail o (synchronousPrefix h W z) w) (P.length+n*L)) (cuts z) ∧
          (cuts z).output.length ≤ k ∧
          (cuts z).output = (P.take k).take (cuts z).output.length ∧
          (cuts z).output <+: P.take k) ∧
        Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
        (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧
        2^n ≤ states.card*(k+1) := by
  obtain ⟨budgetNonnegative,entryCount,stemBase,returnsBase,lowStemBase,lowReturnsBase⟩ :=
    family_endpoint_certificates o s1 s2 P Q h hP hQ hPlen hQlen U V W L hL
      hUlen hVlen hU hV hUWlen
  have hθ : 0 ≤ θ := budgetNonnegative.trans hbudget
  have stemCert := endpoint_certificate_mono _ θ _ _ P h hbudget stemBase
  have returnCert := fun i => endpoint_certificate_mono _ θ _ _ (U i) (W i) hbudget (returnsBase i)

  have highHull := canonical_legal_return_hull s1 U L hL hUlen hU
  have lowHull := canonical_legal_return_hull s2 V L hL hVlen hV
  have wordsEqual : V false = V true := lowHull.2.2.2.2.2.1.mp competingSingleton
  have familyEqual : V = fun _ => V false := by
    funext i
    cases i
    · rfl
    · exact wordsEqual.symm
  have slope := return_slope_control L hL
  have fixed : compose (V false) (canonicalReturnLo V L) = canonicalReturnLo V L := by
    have atLo := lowHull.2.2.2.1 false (canonicalReturnLo V L) le_rfl
      (le_of_eq competingSingleton)
    rw [← competingSingleton] at atLo
    exact le_antisymm atLo.2 atLo.1
  have result := original_synchronous_common_stem action initialConfiguration o θ hθ
    s1 s2 P Q h hP hQ hPlen hQlen U (V false) W L hL hU (hV false)
    hUlen (hVlen false) hUWlen differentReturns
    (canonicalReturnLo U L) (canonicalReturnHi U L) (highHull.2.1 differentReturns)
    highHull.2.2.1 highHull.2.2.2.1 stemCert returnCert
    ((-g)^L) (canonicalReturnLo V L) slope.1 slope.2.1 slope.2.2
    (by rw [hVlen false]) fixed hfeasible k hk sameStem differentStem safety liveness postprocessing
  simpa only [← familyEqual] using result

/-- A block-periodic actual source, with the guard and scalar future also periodic. -/
def PeriodicTail (s : Guard) (w : List Label) (z : ℝ) : Prop :=
  ∃ (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
    path 0 = s ∧ x 0 = z ∧
    (∀ p, nextGuard (path p) (a p) = some (path (p+1))) ∧
    (∀ p, InSupport (path p) (x p)) ∧
    (∀ p, x p = branch (a p) (x (p+1))) ∧
    (∀ p (hp : p < w.length), a p = w[p]) ∧
    (∀ p, a (p+w.length) = a p ∧ x (p+w.length) = x p ∧ path (p+w.length) = path p)

theorem prefix_path_endpoint (s e : Guard) (w : List Label)
    (hw : LegalWord s e w) (a : ℕ → Label) (path : ℕ → Guard)
    (h0 : path 0 = s)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p+1)))
    (hprefix : ∀ p (hp : p < w.length), a p = w[p]) : path w.length = e := by
  induction w generalizing s a path with
  | nil =>
    have hse : s = e := by simpa [LegalWord,walk] using hw
    exact h0.trans hse
  | cons l w ih =>
    cases hn : nextGuard s l with
    | none => simp [LegalWord,walk,hn] at hw
    | some q =>
      have hw' : LegalWord q e w := by simpa [LegalWord,walk,hn] using hw
      have hq : path 1 = q := by
        have he := hedges 0
        rw [h0,hprefix 0 (by simp)] at he
        exact Option.some.inj (he.symm.trans hn)
      have htailPrefix : ∀ p (hp : p < w.length), a (p+1) = w[p] := by
        intro p hp
        exact hprefix (p+1) (by simp; omega)
      have htailEdges : ∀ p, nextGuard (path (p+1)) (a (p+1)) = some (path (p+1+1)) :=
        fun p => hedges (p+1)
      simpa only [List.length_cons,Nat.succ_eq_add_one] using
        ih q hw' (fun p => a (p+1)) (fun p => path (p+1)) hq
          (fun p => by simpa only [Nat.add_assoc] using htailEdges p) htailPrefix

private theorem periodic_tail_of_fixed_return (s : Guard) (w : List Label)
    (hw : LegalWord s s w) (hlen : 0 < w.length) (z : ℝ)
    (hz : InSupport s z) (hfixed : compose w z = z) : PeriodicTail s w z := by
  obtain ⟨a,x,path,h0,hx0,hedges,hsupp,hrec⟩ := lawful_tail s z hz
  obtain ⟨b,y,q,hq0,hy0,hbedges,hbsupp,hbrec,hprefix,hfuture,hyfuture⟩ :=
    prepend_legal_tail s s w hw a x path h0 hedges hsupp hrec
  have hyzero : y 0 = z := by rw [hy0,hx0,hfixed]
  have hyend : y w.length = y 0 := by
    have h := hyfuture 0
    simpa only [Nat.add_zero,hx0,hyzero] using h
  have hqend : q w.length = q 0 :=
    (prefix_path_endpoint s s w hw b q hq0 hbedges hprefix).trans hq0.symm
  have modstep (p : ℕ) : (p+1)%w.length = (p%w.length+1)%w.length := by
    rw [Nat.add_mod p 1 w.length]
    simpa only [Nat.mod_mod] using (Nat.add_mod (p%w.length) 1 w.length).symm
  refine ⟨fun p => b (p%w.length),fun p => y (p%w.length),fun p => q (p%w.length),
    by simpa using hq0,by simpa using hyzero,?_,?_,?_,?_,?_⟩
  · intro p
    change nextGuard (q (p%w.length)) (b (p%w.length)) = some (q ((p+1)%w.length))
    rw [modstep]
    by_cases h : p%w.length+1 < w.length
    · rw [Nat.mod_eq_of_lt h]
      exact hbedges (p%w.length)
    · have hend : p%w.length+1 = w.length := by have hb := Nat.mod_lt p hlen; omega
      rw [hend,Nat.mod_self]
      have he := hbedges (p%w.length)
      rw [hend,hqend] at he
      exact he
  · intro p
    exact hbsupp (p%w.length)
  · intro p
    change y (p%w.length) = branch (b (p%w.length)) (y ((p+1)%w.length))
    rw [modstep]
    by_cases h : p%w.length+1 < w.length
    · rw [Nat.mod_eq_of_lt h]
      exact hbrec (p%w.length)
    · have hend : p%w.length+1 = w.length := by have hb := Nat.mod_lt p hlen; omega
      rw [hend,Nat.mod_self]
      have he := hbrec (p%w.length)
      rw [hend,hyend] at he
      exact he
  · intro p hp
    change b (p%w.length) = w[p]
    rw [Nat.mod_eq_of_lt hp]
    exact hprefix p hp
  · intro p
    simp [Nat.add_mod]

/-- The actual extremal return blocks encode the canonical endpoints. Positive
slope repeats one block; negative slope alternates the two extremal blocks. -/
theorem canonical_periodic_endpoints (s : Guard) (U : Bool → List Label)
    (L : ℕ) (hL : 0 < L) (hlen : ∀ i, (U i).length = L)
    (hlegal : ∀ i, LegalWord s s (U i)) :
    ∃ imin imax : Bool,
      compose (U imin) 0 = min (compose (U false) 0) (compose (U true) 0) ∧
      compose (U imax) 0 = max (compose (U false) 0) (compose (U true) 0) ∧
      PeriodicTail s (if 0 < (-g)^L then U imin else U imin ++ U imax)
        (canonicalReturnLo U L) ∧
      PeriodicTail s (if 0 < (-g)^L then U imax else U imax ++ U imin)
        (canonicalReturnHi U L) := by
  let A : Bool → ℝ := fun i => compose (U i) 0
  let a : ℝ := (-g)^L
  let lo := canonicalReturnLo U L
  let hi := canonicalReturnHi U L
  have slope := return_slope_control L hL
  obtain ⟨ordered,strict,width,contact,invariant,minimal⟩ :=
    canonical_affine_hull A a slope.1 slope.2.1
  change (if 0 < a then
    lo = min (A false) (A true)+a*lo ∧ hi = max (A false) (A true)+a*hi
    else lo = min (A false) (A true)+a*hi ∧ hi = max (A false) (A true)+a*lo) at contact
  have hull := canonical_legal_return_hull s U L hL hlen hlegal
  have hslo : InSupport s lo := hull.2.2.1 lo ⟨le_rfl,hull.1⟩
  have hshi : InSupport s hi := hull.2.2.1 hi ⟨hull.1,le_rfl⟩
  obtain ⟨imin,imax,hmin,hmax⟩ : ∃ imin imax : Bool,
      A imin = min (A false) (A true) ∧ A imax = max (A false) (A true) := by
    rcases le_total (A false) (A true) with h | h
    · exact ⟨false,true,(min_eq_left h).symm,(max_eq_right h).symm⟩
    · exact ⟨true,false,(min_eq_right h).symm,(max_eq_left h).symm⟩
  have affine (i : Bool) (z : ℝ) : compose (U i) z = A i+a*z := by
    simpa only [zero_add,hlen] using literal_source_geometry.2.2.2.1 (U i) 0 z
  refine ⟨imin,imax,hmin,hmax,?_,?_⟩
  · by_cases hpos : 0 < a
    · rw [if_pos hpos]
      apply periodic_tail_of_fixed_return s (U imin) (hlegal imin) (by rw [hlen]; exact hL) lo hslo
      rw [if_pos hpos] at contact
      simpa only [affine,hmin] using contact.1.symm
    · rw [if_neg hpos]
      apply periodic_tail_of_fixed_return s (U imin ++ U imax)
        (legal_append s s s _ _ (hlegal imin) (hlegal imax))
        (by simp only [List.length_append,hlen]; omega) lo hslo
      rw [if_neg hpos] at contact
      rw [literal_source_geometry.2.2.2.2,affine,affine,hmin,hmax,← contact.2,← contact.1]
  · by_cases hpos : 0 < a
    · rw [if_pos hpos]
      apply periodic_tail_of_fixed_return s (U imax) (hlegal imax) (by rw [hlen]; exact hL) hi hshi
      rw [if_pos hpos] at contact
      simpa only [affine,hmax] using contact.2.symm
    · rw [if_neg hpos]
      apply periodic_tail_of_fixed_return s (U imax ++ U imin)
        (legal_append s s s _ _ (hlegal imax) (hlegal imin))
        (by simp only [List.length_append,hlen]; omega) hi hshi
      rw [if_neg hpos] at contact
      rw [literal_source_geometry.2.2.2.2,affine,affine,hmax,hmin,← contact.1,← contact.2]

/-- All actual high-return gaps, across every list and every position. A list
decomposition selects its actual execution prefix without any weight bound. -/
def actualFamilyHighGaps (model : Model) (b : ℝ) (K : ℕ)
    (family : Set (List Return)) : Set ℝ :=
  {gap | ∃ (before : List Return) (a : Return) (after : List Return),
    before ++ a :: after ∈ family ∧ a.r = K ∧
    gap = execute .high before (initial .high model) -
      (lam - b) / g ^ 2 / chi ^ K}

/-- Signed gaps embed into the complete extended real order. In particular,
an empty high-return set has infimum top, and negative gaps are not truncated. -/
noncomputable def actualFamilyDelta (model : Model) (b : ℝ) (K : ℕ)
    (family : Set (List Return)) : EReal :=
  sInf ((fun gap : ℝ => (gap : EReal)) '' actualFamilyHighGaps model b K family)

/-- One epsilon is chosen before every record and both literal source sides.
ActualPairSupply retains every departure observation and the original zero-error
future of that same source. -/
def ActualUniformFamilyMargin (model : Model) (o : Ownership) (b : ℝ)
    (family : Set (List Return)) : Prop :=
  ∃ eps : ℝ, 0 < eps ∧
    ∀ execution ∈ family, ActualPairSupply model o (b - eps) .closed execution

/-- The original uniform epsilon bounds every actual high-return gap, even if
the supplied smaller budget was not assumed to lie in the transition interval. -/
theorem actual_uniform_margin_gap_lower_bound
    (model : Model) (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K)))
    (family : Set (List Return)) (eps : ℝ) (heps : 0 < eps)
    (hsupply : ∀ execution ∈ family,
      ActualPairSupply model o (b - eps) .closed execution) :
    ∀ gap ∈ actualFamilyHighGaps model b K family,
      eps / (g ^ 2 * chi ^ K) ≤ gap := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsqrt0 := Real.sqrt_nonneg (5 : ℝ)
  have hg : 0 < g := by dsimp [g, t]; nlinarith
  have hg2 : 0 < g ^ 2 := pow_pos hg 2
  have hchi : 0 < chi := pow_pos hg 20
  have hchiK : 0 < chi ^ K := pow_pos hchi K
  let c : ℝ := g ^ 2 * chi ^ K
  let q : ℝ := lam - c * hSide .high
  have hc : 0 < c := mul_pos hg2 hchiK
  have threshold_mul (budget : ℝ) :
      ((lam - budget) / g ^ 2 / chi ^ K) * c = lam - budget := by
    dsimp [c]
    field_simp [ne_of_gt hg2, ne_of_gt hchiK] <;> ring
  rintro gap ⟨before, a, after, hfamily, ha, rfl⟩
  let D : ℝ := execute .high before (initial .high model)
  let cost : ℝ := lam - c * D
  have hD : D < hSide .high := by
    simpa [D] using
      ((actual_complete_boundary_geometry model before).1 .high before.length).2
  have hqcost : q < cost := by dsimp [q, cost]; nlinarith
  apply (div_le_iff₀ hc).2
  by_contra hbad
  have hbad' :
      (D - (lam - b) / g ^ 2 / chi ^ K) * c < eps :=
    lt_of_not_ge hbad
  have hsmallcost : b - eps < cost := by
    have hd := threshold_mul b
    dsimp [cost]
    nlinarith
  let lower : ℝ := max q (b - eps)
  let upper : ℝ := min b cost
  have hlowerupper : lower < upper := by
    exact max_lt (lt_min hqb hqcost) (lt_min (by linarith) hsmallcost)
  let budget : ℝ := (lower + upper) / 2
  have hlowerbudget : lower < budget := by dsimp [budget]; linarith
  have hbudgetupper : budget < upper := by dsimp [budget]; linarith
  have hqbudget : q < budget :=
    lt_of_le_of_lt (le_max_left q (b - eps)) hlowerbudget
  have hsmallbudget : b - eps ≤ budget :=
    (le_max_right q (b - eps)).trans hlowerbudget.le
  have hbudgetb : budget < b :=
    lt_of_lt_of_le hbudgetupper (min_le_left b cost)
  have hbudgetcost : budget < cost :=
    lt_of_lt_of_le hbudgetupper (min_le_right b cost)
  have hrecord : ActualPairSupply model o budget .closed (before ++ a :: after) :=
    uniform_closed_supply_mono model o (before ++ a :: after)
      hsmallbudget (hsupply _ hfamily)
  have htrace := (actual_closed_record_supply model o budget
    (before ++ a :: after) K hK hqbudget (hbudgetb.trans hbp)).mp hrecord
  have hguard := ((uniform_guard_trace_iff_split K
    ((lam - budget) / g ^ 2 / chi ^ K) (!o 0) .high
    (before ++ a :: after) (initial .high model)).mp htrace
      before a after rfl).2 ha
  have hweak : (lam - budget) / g ^ 2 / chi ^ K ≤ D := by
    cases hown : o 0 with
    | false =>
        have hstrict : (lam - budget) / g ^ 2 / chi ^ K < D := by
          simpa [hown, D] using hguard
        exact hstrict.le
    | true =>
        simpa [hown, D] using hguard
  have hscaled := mul_le_mul_of_nonneg_right hweak hc.le
  rw [threshold_mul budget] at hscaled
  have hcostbudget : cost ≤ budget := by dsimp [cost]; linarith
  exact (not_lt_of_ge hcostbudget) hbudgetcost

/-- Original 62.16, including the fixed anchor's input X_H. -/
noncomputable def actualAutomaticCost (K : ℕ) : ℝ :=
  max (max (lam - g ^ 2 * chi * xSide .high)
    (lam - g ^ 2 * chi ^ (K - 1) * aSide .high)) (lam - g ^ 6)

/-- The original automatic bound is below q_K and pays the nonactive slots,
the fixed anchor, every stem and every return with r<K. -/
theorem actual_automatic_cost_envelope (K : ℕ) (hK : 2 ≤ K) :
    actualAutomaticCost K < lam - g ^ 2 * chi ^ K * hSide .high ∧
    lam - rho ≤ actualAutomaticCost K ∧
    lam - g ^ 2 * chi * xSide .high ≤ actualAutomaticCost K ∧
    (∀ D : ℝ, aSide .high < D →
      lam - g ^ 2 * chi * D < actualAutomaticCost K) ∧
    (∀ (r : ℕ) (D : ℝ), r < K → aSide .high < D →
      lam - g ^ 2 * chi ^ r * D < actualAutomaticCost K) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hs0 := Real.sqrt_nonneg (5 : ℝ)
  have root : g ^ 2 + 4 * g = 1 := by dsimp [g, t]; nlinarith
  have gp : 0 < g := by dsimp [g, t]; nlinarith
  have gq : g < 1 / 4 := by nlinarith
  have gp1 : g < 1 := by linarith
  have g2p : 0 < g ^ 2 := pow_pos gp 2
  have rp : 0 < rho := pow_pos gp 6
  have cp : 0 < chi := pow_pos gp 20
  have r1 : rho < 1 := pow_lt_one₀ gp.le gp1 (by decide)
  have c1 : chi < 1 := pow_lt_one₀ gp.le gp1 (by decide)
  have chi4 : chi ≤ g ^ 4 :=
    pow_le_pow_of_le_one gp.le gp1.le (by decide)
  have rbound : rho < 1 / 4096 := by
    have h := pow_lt_pow_left₀ gq gp.le (by decide : (6 : ℕ) ≠ 0)
    norm_num [rho] at h ⊢
    exact h
  have cbound : chi < 1 / 256 := by
    have h := pow_lt_pow_left₀ gq gp.le (by decide : (4 : ℕ) ≠ 0)
    norm_num at h
    exact lt_of_le_of_lt chi4 h
  have Hp : 0 < hSide .high := by dsimp [hSide]; linarith
  have H1 : hSide .high < 1 := by dsimp [hSide]; linarith
  have Ap : 0 < aSide .high := mul_pos (sub_pos.mpr r1) Hp
  have gap : chi * hSide .high < aSide .high := by
    have h := mul_lt_mul_of_pos_right (show chi < 1 - rho by linarith) Hp
    exact h
  have Xlower : aSide .high < xSide .high := by
    simpa only [List.take_nil, execute, initial] using
      ((actual_complete_boundary_geometry .original []).1 .high 0).1
  have km : 1 ≤ K - 1 := by omega
  have ckm : chi ^ (K - 1) ≤ chi := by
    simpa only [pow_one] using pow_le_pow_of_le_one cp.le c1.le km
  have cK2 : chi ^ K ≤ chi ^ 2 :=
    pow_le_pow_of_le_one cp.le c1.le hK
  have cK : chi ^ K ≤ chi := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one cp.le c1.le (show 1 ≤ K by omega)
  have pkm : 0 < chi ^ (K - 1) := pow_pos cp (K - 1)
  have pk : chi ^ K = chi ^ (K - 1) * chi := by
    rw [← pow_succ]
    congr 1
    omega
  have lowQ : lam - g ^ 2 * chi ^ (K - 1) * aSide .high <
      lam - g ^ 2 * chi ^ K * hSide .high := by
    have h := mul_lt_mul_of_pos_left gap (mul_pos g2p pkm)
    rw [pk]
    nlinarith
  have anchorQ : lam - g ^ 2 * chi * xSide .high <
      lam - g ^ 2 * chi ^ K * hSide .high := by
    have h1 := mul_lt_mul_of_pos_left Xlower cp
    have h2 := mul_lt_mul_of_pos_left gap cp
    have h3 := mul_le_mul_of_nonneg_right cK2 Hp.le
    have h4 : chi ^ K * hSide .high < chi * xSide .high := by nlinarith
    have h5 := mul_lt_mul_of_pos_left h4 g2p
    nlinarith
  have cKh : chi ^ K * hSide .high < chi :=
    lt_of_lt_of_le (by simpa using
      mul_lt_mul_of_pos_left H1 (pow_pos cp K)) cK
  have powerId : g ^ 2 * g ^ 4 = rho := by dsimp [rho]; ring
  have costSmall : g ^ 2 * chi ^ K * hSide .high < rho := by
    have h1 := mul_lt_mul_of_pos_left cKh g2p
    have h2 := mul_le_mul_of_nonneg_left chi4 g2p.le
    rw [powerId] at h2
    nlinarith
  have inactiveQ : lam - g ^ 6 < lam - g ^ 2 * chi ^ K * hSide .high := by
    simpa only [rho] using (sub_lt_sub_left costSmall lam)
  have lowLe : lam - g ^ 2 * chi ^ (K - 1) * aSide .high ≤
      actualAutomaticCost K :=
    (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨max_lt (max_lt anchorQ lowQ) inactiveQ, ?_, ?_, ?_, ?_⟩
  · simpa only [rho, actualAutomaticCost] using
      (le_max_right
        (max (lam - g ^ 2 * chi * xSide .high)
          (lam - g ^ 2 * chi ^ (K - 1) * aSide .high))
        (lam - g ^ 6))
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · intro D hD
    have h1 := mul_lt_mul_of_pos_left hD cp
    have h2 := mul_le_mul_of_nonneg_right ckm Ap.le
    have h3 : chi ^ (K - 1) * aSide .high < chi * D := by linarith
    have h4 := mul_lt_mul_of_pos_left h3 g2p
    apply lt_of_lt_of_le _ lowLe
    nlinarith
  · intro r D hr hD
    have hDp : 0 < D := Ap.trans hD
    have hpower : chi ^ (K - 1) ≤ chi ^ r :=
      pow_le_pow_of_le_one cp.le c1.le (show r ≤ K - 1 by omega)
    have h1 := mul_lt_mul_of_pos_left hD pkm
    have h2 := mul_le_mul_of_nonneg_right hpower hDp.le
    have h3 : chi ^ (K - 1) * aSide .high < chi ^ r * D := by linarith
    have h4 := mul_lt_mul_of_pos_left h3 g2p
    apply lt_of_lt_of_le _ lowLe
    nlinarith

/-- This sufficiency needs only budget>C_auto, including budgets below q_K.
It retains the cap and each actual high-position cost as separate hypotheses. -/
theorem actual_capped_strict_supply_of_high_costs
    (model : Model) (o : Ownership) (K : ℕ) (hK : 2 ≤ K)
    (budget : ℝ) (hbudget : actualAutomaticCost K < budget)
    (execution : List Return)
    (hcap : ∀ a ∈ execution, a.r ≤ K)
    (hhigh : ∀ (before : List Return) (a : Return) (after : List Return),
      execution = before ++ a :: after → a.r = K →
        lam - g ^ 2 * chi ^ K *
          execute .high before (initial .high model) < budget) :
    ActualPairSupply model o budget .strict execution := by
  have hauto := actual_automatic_cost_envelope K hK
  apply (actual_strict_cost_supply model o budget execution
    (hauto.2.1.trans_lt hbudget)).mpr
  have hwhole : aSide .high < execute .high execution (initial .high model) := by
    simpa only [List.take_length] using
      ((actual_complete_boundary_geometry model execution).1 .high execution.length).1
  refine ⟨(hauto.2.2.2.1 _ hwhole).trans hbudget,
    fun _ => hauto.2.2.1.trans_lt hbudget, ?_⟩
  apply (exact_control_iff_split .high budget execution (initial .high model)).mpr
  intro before a after hsplit
  by_cases ha : a.r = K
  · simpa only [ha] using hhigh before a after hsplit ha
  · have hmem : a ∈ execution := by rw [hsplit]; simp
    have hr : a.r < K := by
      have hc := hcap a hmem
      omega
    have hD : aSide .high < execute .high before (initial .high model) := by
      simpa only [List.take_length] using
        ((actual_complete_boundary_geometry model before).1 .high before.length).1
    exact (hauto.2.2.2.2 a.r _ hr hD).trans hbudget

/-- Original 62.6's numerical choice, with its separate empty-high-position
branch. A nonempty positive gap infimum is finite, so toReal preserves it. -/
noncomputable def actualExactFamilyMargin (model : Model) (b : ℝ) (K : ℕ)
    (family : Set (List Return)) : ℝ := by
  classical
  exact if (actualFamilyHighGaps model b K family).Nonempty then
    min (b - actualAutomaticCost K)
      ((g ^ 2 * chi ^ K) * (actualFamilyDelta model b K family).toReal) / 2
  else (b - actualAutomaticCost K) / 2

/-- The exact displayed sufficient margin of original 62.6 works for every
whole paired record and its original zero-error future, across the entire family. -/
theorem actual_exact_uniform_family_margin
    (model : Model) (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K)))
    (family : Set (List Return))
    (hcap : ∀ execution ∈ family, ∀ a ∈ execution, a.r ≤ K)
    (hdelta : 0 < actualFamilyDelta model b K family) :
    let eps := actualExactFamilyMargin model b K family
    0 < eps ∧ ∀ execution ∈ family,
      ActualPairSupply model o (b - eps) .strict execution := by
  classical
  have hauto := actual_automatic_cost_envelope K hK
  have hCb : actualAutomaticCost K < b := hauto.1.trans hqb
  have hbC : 0 < b - actualAutomaticCost K := sub_pos.mpr hCb
  let eps := actualExactFamilyMargin model b K family
  change 0 < eps ∧ ∀ execution ∈ family,
    ActualPairSupply model o (b - eps) .strict execution
  by_cases hnonempty : (actualFamilyHighGaps model b K family).Nonempty
  · have highExists := hnonempty
    obtain ⟨witness, hwitness⟩ := highExists
    have hupper : actualFamilyDelta model b K family ≤ (witness : EReal) :=
      sInf_le ⟨witness, hwitness, rfl⟩
    have hnotTop : actualFamilyDelta model b K family ≠ ⊤ :=
      ne_of_lt (hupper.trans_lt (EReal.coe_lt_top witness))
    have hnotBot : actualFamilyDelta model b K family ≠ ⊥ :=
      ne_of_gt ((show (⊥ : EReal) < 0 by simp).trans hdelta)
    let delta := (actualFamilyDelta model b K family).toReal
    have hdeltaReal : 0 < delta := EReal.toReal_pos hdelta hnotTop
    have hcoe : (delta : EReal) = actualFamilyDelta model b K family :=
      EReal.coe_toReal hnotTop hnotBot
    have hgap : ∀ gap ∈ actualFamilyHighGaps model b K family, delta ≤ gap := by
      intro gap hmem
      apply EReal.coe_le_coe_iff.mp
      rw [hcoe]
      exact sInf_le ⟨gap, hmem, rfl⟩
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
    have hs0 := Real.sqrt_nonneg (5 : ℝ)
    have hg : 0 < g := by dsimp [g, t]; nlinarith
    have hg2 : 0 < g ^ 2 := pow_pos hg 2
    have hchi : 0 < chi := pow_pos hg 20
    have hchiK : 0 < chi ^ K := pow_pos hchi K
    let c : ℝ := g ^ 2 * chi ^ K
    have hc : 0 < c := mul_pos hg2 hchiK
    have hcdelta : 0 < c * delta := mul_pos hc hdeltaReal
    have hepsEq : eps = min (b - actualAutomaticCost K) (c * delta) / 2 := by
      simp only [eps, actualExactFamilyMargin, if_pos hnonempty, c, delta]
    have heps : 0 < eps := by
      rw [hepsEq]
      exact div_pos (lt_min hbC hcdelta) (by norm_num)
    have hepsAuto : eps < b - actualAutomaticCost K := by
      have hm := min_le_left (b - actualAutomaticCost K) (c * delta)
      rw [hepsEq]
      linarith
    have hepsHigh : eps < c * delta := by
      have hm := min_le_right (b - actualAutomaticCost K) (c * delta)
      rw [hepsEq]
      linarith
    have hbudget : actualAutomaticCost K < b - eps := by linarith
    have threshold_mul :
        ((lam - b) / g ^ 2 / chi ^ K) * c = lam - b := by
      dsimp [c]
      field_simp [ne_of_gt hg2, ne_of_gt hchiK] <;> ring
    refine ⟨heps, ?_⟩
    intro execution hexecution
    apply actual_capped_strict_supply_of_high_costs model o K hK
      (b - eps) hbudget execution (hcap execution hexecution)
    intro before a after hsplit ha
    have hmember : execute .high before (initial .high model) -
        (lam - b) / g ^ 2 / chi ^ K ∈ actualFamilyHighGaps model b K family := by
      refine ⟨before, a, after, ?_, ha, rfl⟩
      rw [← hsplit]
      exact hexecution
    have hlower := mul_le_mul_of_nonneg_right (hgap _ hmember) hc.le
    change lam - c * execute .high before (initial .high model) < b - eps
    nlinarith
  · have hepsEq : eps = (b - actualAutomaticCost K) / 2 := by
      simp only [eps, actualExactFamilyMargin, if_neg hnonempty]
    have heps : 0 < eps := by rw [hepsEq]; positivity
    have hbudget : actualAutomaticCost K < b - eps := by rw [hepsEq]; linarith
    refine ⟨heps, ?_⟩
    intro execution hexecution
    apply actual_capped_strict_supply_of_high_costs model o K hK
      (b - eps) hbudget execution (hcap execution hexecution)
    intro before a after hsplit ha
    have hmember : execute .high before (initial .high model) -
        (lam - b) / g ^ 2 / chi ^ K ∈ actualFamilyHighGaps model b K family := by
      refine ⟨before, a, after, ?_, ha, rfl⟩
      rw [← hsplit]
      exact hexecution
    exact (hnonempty ⟨_, hmember⟩).elim

/-- Original 62.6 for arbitrary families of whole actual return records.
The single positive margin includes every original literal zero-error future. -/
theorem actual_uniform_family_margin_iff
    (model : Model) (o : Ownership) (b : ℝ) (K : ℕ) (hK : 2 ≤ K)
    (hqb : lam - g ^ 2 * chi ^ K * hSide .high < b)
    (hbp : b < lam - g ^ 2 * chi ^ K *
      (aSide .high / (1 - rho * chi ^ K)))
    (family : Set (List Return))
    (hcap : ∀ execution ∈ family, ∀ a ∈ execution, a.r ≤ K) :
    ActualUniformFamilyMargin model o b family ↔
      0 < actualFamilyDelta model b K family := by
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsqrt0 := Real.sqrt_nonneg (5 : ℝ)
  have hg : 0 < g := by dsimp [g, t]; nlinarith
  have hg2 : 0 < g ^ 2 := pow_pos hg 2
  have hchi : 0 < chi := pow_pos hg 20
  have hchiK : 0 < chi ^ K := pow_pos hchi K
  let c : ℝ := g ^ 2 * chi ^ K
  have hc : 0 < c := mul_pos hg2 hchiK
  constructor
  · rintro ⟨eps, heps, hsupply⟩
    have hbound := actual_uniform_margin_gap_lower_bound
      model o b K hK hqb hbp family eps heps hsupply
    have hinf : ((eps / c : ℝ) : EReal) ≤ actualFamilyDelta model b K family := by
      unfold actualFamilyDelta
      apply le_sInf
      rintro _ ⟨gap, hgap, rfl⟩
      exact EReal.coe_le_coe (hbound gap hgap)
    have hpos : (0 : EReal) < ((eps / c : ℝ) : EReal) := by
      exact_mod_cast (div_pos heps hc)
    exact hpos.trans_le hinf
  · intro hdelta
    obtain ⟨heps, hsupply⟩ := actual_exact_uniform_family_margin
      model o b K hK hqb hbp family hcap hdelta
    refine ⟨actualExactFamilyMargin model b K family, heps, ?_⟩
    intro execution hexecution j
    rcases hsupply execution hexecution j with ⟨err, herr, hread, hzero, hfuture⟩
    refine ⟨err, ?_, hread, hzero, hfuture⟩
    intro p
    exact (herr p).le


end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
