/- GID: D5/S3/Arith/FibonacciAtomic/BottomSiblingBlockResolution
   generality: I
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Actual reset sources satisfy the complete global bottom-sibling criterion. -/

import D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
import D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockResolution

open D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open D5.S3.Arith.ZeckendorfFutureKernel (value value_append legal)
open D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy (primePowerProjection)
open D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution (depth)
open D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion (jointReadout)

/-- The full actual-source bottom-sibling theorem, including all original End
readouts and globally attached successful-word queries. -/
theorem result (H t : Nat) (hH : 2 ≤ H) (u v : ZMod H)
    (hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod H) = u ∧
      ((nextRow source).2 : ZMod H) = v) :
    Target H t hH u v hrow := by
  have probe_gcd_depth (H : Nat) (hH : 2 ≤ H) (p : H.primeFactors)
      (r c : ZMod H) :
      (Nat.gcd ((r - c).val + H) H).factorization p.val =
        depth p.val (H.factorization p.val)
          (ZMod.cast c) (ZMod.cast r) := by
    classical
    have hH0 : H ≠ 0 := by omega
    letI : NeZero H := ⟨hH0⟩
    have hp : p.val.Prime := Nat.prime_of_mem_primeFactors p.property
    have hh : 1 ≤ H.factorization p.val :=
      hp.factorization_pos_of_dvd hH0 (Nat.dvd_of_mem_primeFactors p.property)
    letI : Fact p.val.Prime := ⟨hp⟩
    let h := H.factorization p.val
    let z := (r-c).val + H
    have hz0 : z ≠ 0 := by dsimp [z]; omega
    have bound := (D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
      p.val h hh).1 (0 : ZMod (p.val ^ h)) (z : ZMod (p.val ^ h))
    have threshold (j : Nat) (hj : j ≤ h) :
        j ≤ depth p.val h 0 (z : ZMod (p.val ^ h)) ↔
          j ≤ z.factorization p.val := by
      have ht := bound.2 j hj
      rw [ZMod.cast_natCast (pow_dvd_pow p.val hj), ZMod.cast_zero,
        ZMod.natCast_eq_zero_iff] at ht
      exact ht.trans (hp.pow_dvd_iff_le_factorization hz0)
    have hl := (threshold (min (z.factorization p.val) h) (min_le_right _ _)).2
      (min_le_left _ _)
    have hu := (threshold _ bound.1).1 le_rfl
    have hdepth : (Nat.gcd z H).factorization p.val =
        depth p.val h 0 (z : ZMod (p.val ^ h)) := by
      rw [Nat.factorization_gcd hz0 hH0, Finsupp.inf_apply]
      change min (z.factorization p.val) h = _
      exact Nat.le_antisymm hl (le_min hu bound.1)
    rw [hdepth]
    have hcastH : (H : ZMod (p.val ^ h)) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (Nat.ordProj_dvd H p.val)
    have hcastz : (z : ZMod (p.val ^ h)) = ZMod.cast r - ZMod.cast c := by
      dsimp [z]
      rw [Nat.cast_add, hcastH, add_zero]
      have hc : (ZMod.cast (r-c) : ZMod (p.val ^ h)) =
          ZMod.cast r - ZMod.cast c :=
        ZMod.cast_sub (Nat.ordProj_dvd H p.val) r c
      simpa only [ZMod.cast_eq_val] using hc
    have hcomp (j : Nat) (hj : j ≤ h) (q : ZMod H) :
        (ZMod.cast (ZMod.cast q : ZMod (p.val ^ h)) : ZMod (p.val ^ j)) =
          ZMod.cast q := by
      exact DFunLike.congr_fun (ZMod.castHom_comp (pow_dvd_pow p.val hj)
        (Nat.ordProj_dvd H p.val)) q
    have threshold_eq (j : Nat) (hj : j ≤ h) :
        ((ZMod.cast (z : ZMod (p.val ^ h)) : ZMod (p.val ^ j)) = 0) ↔
        ((ZMod.cast (ZMod.cast r : ZMod (p.val ^ h)) : ZMod (p.val ^ j)) =
          (ZMod.cast (ZMod.cast c : ZMod (p.val ^ h)) : ZMod (p.val ^ j))) := by
      have hc := congrArg (fun q : ZMod (p.val ^ h) =>
        (ZMod.cast q : ZMod (p.val ^ j))) hcastz
      rw [ZMod.cast_sub (pow_dvd_pow p.val hj)] at hc
      constructor
      · intro hz
        apply sub_eq_zero.mp
        exact hc.symm.trans hz
      · intro hrc
        rw [hc]
        exact sub_eq_zero.mpr hrc
    apply le_antisymm
    · have hd := bound.1
      have ht := (D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
        p.val h hh).1 (ZMod.cast c) (ZMod.cast r)
      apply (ht.2 _ hd).2
      have hs := (bound.2 _ hd).1 le_rfl
      exact (threshold_eq _ hd).1 (by simpa only [ZMod.cast_zero] using hs)
    · have hd := (D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
        p.val h hh).1 (ZMod.cast c) (ZMod.cast r)
      apply (bound.2 _ hd.1).2
      have hs := (hd.2 _ hd.1).1 le_rfl
      simpa only [ZMod.cast_zero] using (threshold_eq _ hd.1).2 hs

  have probe_local_criterion (p e : Nat) [Fact p.Prime] (he : 1 ≤ e)
      (S : Finset (ZMod (p ^ e))) :
      (∀ b : ZMod (p ^ (e-1)),
        (S.filter fun a => primePowerProjection p (Nat.sub_le e 1) a = b).card ≥ p-1) ↔
      Function.Injective (jointReadout (fun c : S => depth p e c.val)) := by
    classical
    let π := primePowerProjection p (Nat.sub_le e 1)
    have hr := D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result p e he
    rcases hr with ⟨_,_,_,_,_,_, fibers, criterion,_,_⟩
    have hcard (b : ZMod (p ^ (e-1))) :
        (S.filter fun a => π a = b).card +
        (Sᶜ.filter fun a => π a = b).card = p := by
      have hpart := Finset.card_filter_add_card_filter_not
        (s := Finset.univ.filter fun a : ZMod (p ^ e) => π a = b)
        (p := fun a => a ∈ S)
      have hfirst : ((Finset.univ.filter fun a : ZMod (p ^ e) => π a = b).filter
          fun a => a ∈ S) = S.filter (fun a => π a = b) := by
        ext a
        simp [and_comm]
      have hsecond : ((Finset.univ.filter fun a : ZMod (p ^ e) => π a = b).filter
          fun a => ¬a ∈ S) = Sᶜ.filter (fun a => π a = b) := by
        ext a
        simp [and_comm]
      rw [hfirst, hsecond] at hpart
      exact hpart.trans (fibers b)
    rw [criterion S]
    constructor
    · intro h b
      have hc :
          (S.filter fun a => primePowerProjection p (Nat.sub_le e 1) a = b).card +
          (Sᶜ.filter fun a => primePowerProjection p (Nat.sub_le e 1) a = b).card = p := by
        simpa only [π] using hcard b
      have hs := h b
      omega
    · intro h b
      have hc :
          (S.filter fun a => primePowerProjection p (Nat.sub_le e 1) a = b).card +
          (Sᶜ.filter fun a => primePowerProjection p (Nat.sub_le e 1) a = b).card = p := by
        simpa only [π] using hcard b
      have hs := h b
      omega

  have probe_query_axes (H : Nat) (hH : 2 ≤ H)
      (S : Finset (ZMod H)) (r s : ZMod H) :
      (∀ c : S, Nat.gcd ((r - c.val).val + H) H =
          Nat.gcd ((s - c.val).val + H) H) ↔
        ∀ p : H.primeFactors,
          ∀ d : S.image (fun c : ZMod H =>
            (ZMod.cast c : ZMod (p.val ^ H.factorization p.val))),
            depth p.val (H.factorization p.val) d.val (ZMod.cast r) =
              depth p.val (H.factorization p.val) d.val (ZMod.cast s) := by
    classical
    have hH0 : H ≠ 0 := by omega
    constructor
    · intro h p d
      obtain ⟨c, hcS, hcd⟩ := Finset.mem_image.mp d.property
      have heq := h ⟨c,hcS⟩
      have hf := congrArg (fun n : Nat => n.factorization p.val) heq
      rw [probe_gcd_depth H hH p r c, probe_gcd_depth H hH p s c] at hf
      have hd : d.val = (ZMod.cast c : ZMod (p.val ^ H.factorization p.val)) := hcd.symm
      simpa only [hd] using hf
    · intro h c
      apply Nat.eq_of_factorization_eq (Nat.gcd_ne_zero_right hH0)
        (Nat.gcd_ne_zero_right hH0)
      intro q
      by_cases hq : q ∈ H.primeFactors
      · let p : H.primeFactors := ⟨q,hq⟩
        let d : S.image (fun c : ZMod H =>
            (ZMod.cast c : ZMod (p.val ^ H.factorization p.val))) :=
          ⟨ZMod.cast c.val, Finset.mem_image.mpr ⟨c.val, c.property, rfl⟩⟩
        have hd := h p d
        change depth p.val (H.factorization p.val) (ZMod.cast c.val) (ZMod.cast r) =
          depth p.val (H.factorization p.val) (ZMod.cast c.val) (ZMod.cast s) at hd
        simpa only [p] using
          (probe_gcd_depth H hH p r c.val).trans (hd.trans
            (probe_gcd_depth H hH p s c.val).symm)
      · have hfact : H.factorization q = 0 := by
          exact Finsupp.notMem_support_iff.1
            (by simpa only [Nat.support_factorization] using hq)
        have hrle := (Nat.factorization_le_iff_dvd
          (Nat.gcd_ne_zero_right hH0) hH0).2
          (Nat.gcd_dvd_right ((r-c.val).val+H) H) q
        have hsle := (Nat.factorization_le_iff_dvd
          (Nat.gcd_ne_zero_right hH0) hH0).2
          (Nat.gcd_dvd_right ((s-c.val).val+H) H) q
        omega

  have probe_equivPi_apply (H : Nat) (hH : 2 ≤ H) (z : ZMod H) (p : H.primeFactors) :
      (ZMod.equivPi H (by omega : H ≠ 0) z) p = ZMod.cast z := by
    have hH0 : H ≠ 0 := by omega
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    rw [map_intCast]
    change (k : ZMod (p.val ^ H.factorization p.val)) =
      ZMod.cast (k : ZMod H)
    exact (map_intCast (ZMod.castHom (Nat.ordProj_dvd H p.val)
      (ZMod (p.val ^ H.factorization p.val))) k).symm

  have probe_global_crt_injective (H : Nat) (hH : 2 ≤ H)
      (S : Finset (ZMod H)) :
      Function.Injective (fun r : ZMod H =>
        fun c : S => Nat.gcd ((r - c.val).val + H) H) ↔
      ∀ p : H.primeFactors,
        Function.Injective (jointReadout
          (fun d : S.image (fun c : ZMod H =>
            (ZMod.cast c : ZMod (p.val ^ H.factorization p.val))) =>
            depth p.val (H.factorization p.val) d.val)) := by
    classical
    have hH0 : H ≠ 0 := by omega
    let E := ZMod.equivPi H hH0
    have projection (z : ZMod H) (p : H.primeFactors) : E z p = ZMod.cast z :=
      probe_equivPi_apply H hH z p
    constructor
    · intro hinj p a b hab
      let ar : ∀ q : H.primeFactors, ZMod (q.val ^ H.factorization q.val) :=
        fun q => if h : q = p then h.symm ▸ a else 0
      let br : ∀ q : H.primeFactors, ZMod (q.val ^ H.factorization q.val) :=
        fun q => if h : q = p then h.symm ▸ b else 0
      let r := E.symm ar
      let s := E.symm br
      have hlocal (q : H.primeFactors) :
          (ZMod.cast r : ZMod (q.val ^ H.factorization q.val)) = ar q ∧
          (ZMod.cast s : ZMod (q.val ^ H.factorization q.val)) = br q := by
        constructor
        · exact (projection r q).symm.trans (congrFun (E.apply_symm_apply ar) q)
        · exact (projection s q).symm.trans (congrFun (E.apply_symm_apply br) q)
      have hquery : ∀ c : S,
          Nat.gcd ((r - c.val).val + H) H =
            Nat.gcd ((s - c.val).val + H) H := by
        apply (probe_query_axes H hH S r s).2
        intro q d
        rcases hlocal q with ⟨hr,hs⟩
        rw [hr,hs]
        by_cases hqp : q = p
        · subst q
          simpa only [jointReadout, ar, br, dif_pos, Subtype.coe_mk] using congrFun hab d
        · simp [ar, br, hqp]
      have hrs : r = s := hinj (funext hquery)
      have heq := congrFun (congrArg E hrs) p
      simpa [r,s,ar,br] using heq
    · intro h r s hrs
      apply E.injective
      funext p
      rw [projection r p, projection s p]
      apply h p
      funext d
      exact (probe_query_axes H hH S r s).1 (congrFun hrs) p d

  have probe_actual_query (H t : Nat) (hH : 2 ≤ H) (u v : ZMod H)
      (source : KnownRowFiber H u v) (w : SuccessfulWord t) :
      rawGcd H source.val w.val = some (Nat.gcd
        (((sourceNumber source.val : ZMod H) -
          (-value u v (flatten w.val))).val + H) H) := by
    letI : NeZero H := ⟨by omega⟩
    have run_append (q : Option (Bool × Bool)) (a b : List Window) :
        run q (a ++ b) = run (run q a) b := by
      induction a generalizing q with
      | nil => rfl
      | cons c cs ih => exact ih (step q c)
    have value_cast (a b : Nat) (bs : List Bool) :
        ((value (R := Nat) a b bs : Nat) : ZMod H) =
          value (a : ZMod H) (b : ZMod H) bs := by
      induction bs generalizing a b with
      | nil => simp [value]
      | cons c cs ih =>
        cases c
        · simp only [value, Bool.false_eq_true, ↓reduceIte, zero_add]
          simpa only [Nat.cast_add] using ih b (a + b)
        · simp only [value, ↓reduceIte, Nat.cast_add]
          simpa only [Nat.cast_add] using congrArg (fun z => (a : ZMod H) + z)
            (ih b (a + b))
    have hraw : rawGcd H source.val w.val = some (Nat.gcd
        (sourceNumber source.val + value (nextRow source.val).1
          (nextRow source.val).2 (flatten w.val)) H) := by
      unfold rawGcd observe
      rw [run_append, source.val.terminal]
      have hexec := (execution true true w.val).1.2
      have hsuccess : endable (run (some (true, true)) w.val) = true := w.property.2
      have hlegal : legal true (flatten w.val) := by
        by_contra hn
        have hnone := (execution true true w.val).2.2 hn
        rw [hnone] at hsuccess
        simp [endable] at hsuccess
      rw [hexec hlegal]
      have hpair : endable (some
          (List.foldl (fun _ b => last b) true w.val,
           List.foldl (fun _ b => nonzero b) true w.val)) = true := by
        simpa [hexec hlegal] using hsuccess
      rw [hpair]
      have hvalue := value_append (flatten source.val.past) (flatten w.val) (2 : Nat) 3
      simp only [sourceNumber, nextRow]
      rw [show flatten (source.val.past ++ w.val) =
        flatten source.val.past ++ flatten w.val by simp [flatten], hvalue]
      simp [Nat.add_assoc]
    have hval : value ((nextRow source.val).1 : ZMod H)
        ((nextRow source.val).2 : ZMod H) (flatten w.val) =
        value u v (flatten w.val) := by
      rw [source.property.1, source.property.2]
    have hcast :
        ((sourceNumber source.val + value (nextRow source.val).1
          (nextRow source.val).2 (flatten w.val) : Nat) : ZMod H) =
        (((sourceNumber source.val : ZMod H) -
          (-value u v (flatten w.val))).val + H : Nat) := by
      rw [Nat.cast_add, Nat.cast_add, value_cast, hval, ZMod.natCast_zmod_val]
      simp only [ZMod.natCast_self, add_zero]
      ring
    exact hraw.trans (congrArg some (Nat.ModEq.gcd_eq
      ((ZMod.natCast_eq_natCast_iff _ _ H).mp hcast)))

  have probe_finite_scan {I X : Type} [Fintype I] [DecidableEq I]
      (read : I → X → Option Nat) :
      ∃ protocol : D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.PassiveProtocol
          I (fun _ => Option Nat),
        ∀ x y, D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.runPassiveProtocol
          read protocol x =
          D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.runPassiveProtocol
          read protocol y → ∀ i, read i x = read i y := by
    open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound in
    let scan : List I → PassiveProtocol I (fun _ => Option Nat) :=
      fun l => l.foldr (fun i rest => .query i (fun _ => rest)) .stop
    have scan_reads (l : List I) (x y : X)
        (h : D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.runPassiveProtocol
          read (scan l) x =
          D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.runPassiveProtocol
          read (scan l) y) :
        ∀ i ∈ l, read i x = read i y := by
      induction l with
      | nil => simp
      | cons a as ih =>
        intro i hi
        simp only [scan, List.foldr_cons,
          D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.runPassiveProtocol]
          at h
        rcases List.cons.inj h with ⟨hhead, htail⟩
        have ha : read a x = read a y := by
          exact eq_of_heq (by simpa only [Sigma.mk.inj_iff, true_and] using hhead)
        rcases List.mem_cons.mp hi with rfl | hi
        · exact ha
        · exact ih htail i hi
    refine ⟨scan Finset.univ.toList, ?_⟩
    intro x y h i
    exact scan_reads _ x y h i (by simp)

  have probe_actual_ident_iff_model (H t : Nat) (hH : 2 ≤ H) (u v : ZMod H)
      (hrow : ∃ source : ActualPrefix,
        ((nextRow source).1 : ZMod H) = u ∧
        ((nextRow source).2 : ZMod H) = v)
      (available : Finset (SuccessfulWord t)) :
      FiniteIdentifiable t H u v available ↔
        Function.Injective (fun r : ZMod H => fun w : ↑available =>
          Nat.gcd ((r - (-value u v (flatten w.val.val))).val + H) H) := by
    classical
    let read (w : ↑available) (source : KnownRowFiber H u v) :=
      rawGcd H source.val w.val.val
    let model (r : ZMod H) (w : ↑available) :=
      Nat.gcd ((r - (-value u v (flatten w.val.val))).val + H) H
    let residue (source : KnownRowFiber H u v) : ZMod H := sourceNumber source.val
    have read_eq (w : ↑available) (source : KnownRowFiber H u v) :
        read w source = some (model (residue source) w) := by
      exact probe_actual_query H t hH u v source w.val
    have full : Function.Surjective residue := by
      obtain ⟨j, hj⟩ := actual_common_depth_fullness H hH u v hrow
      intro r
      obtain ⟨source, _, hs⟩ := hj r
      exact ⟨source, hs⟩
    constructor
    · rintro ⟨protocol, identifies⟩ r s hrs
      obtain ⟨x, rfl⟩ := full r
      obtain ⟨y, rfl⟩ := full s
      have hread : ∀ w, read w x = read w y := by
        intro w
        rw [read_eq, read_eq]
        exact congrArg some (congrFun hrs w)
      have hjoint :
          D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion.jointReadout
            read x =
          D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion.jointReadout
            read y := funext hread
      obtain ⟨factor, hf⟩ :=
        D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.passive_adaptive_transcript_upper_bound
          read protocol
      have htrace :
          D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.runPassiveProtocol
            read protocol x =
          D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound.runPassiveProtocol
            read protocol y := by
        calc
          _ = factor
            (D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion.jointReadout
              read x) := congrFun hf x
          _ = factor
            (D5.S3.ConceptDynamics.Faithfulness.JointFaithfulnessLeibnizCriterion.jointReadout
              read y) := congrArg factor hjoint
          _ = _ := (congrFun hf y).symm
      exact identifies htrace
    · intro hinj
      obtain ⟨protocol, scans⟩ := probe_finite_scan read
      refine ⟨protocol, ?_⟩
      intro x y htrace
      apply hinj
      funext w
      have hread := scans x y htrace w
      rw [read_eq, read_eq] at hread
      exact Option.some.inj hread

  have probe_complete_criterion (H t : Nat) (hH : 2 ≤ H) (u v : ZMod H)
      (hrow : ∃ source : ActualPrefix,
        ((nextRow source).1 : ZMod H) = u ∧
        ((nextRow source).2 : ZMod H) = v)
      (available : Finset (SuccessfulWord t)) :
      FiniteIdentifiable t H u v available ↔ BottomBlocks t H u v available := by
    classical
    let S : Finset (ZMod H) := centers t H u v available
    have hmodel :
        Function.Injective (fun r : ZMod H => fun w : ↑available =>
          Nat.gcd ((r - (-value u v (flatten w.val.val))).val + H) H) ↔
        Function.Injective (fun r : ZMod H => fun c : S =>
          Nat.gcd ((r - c.val).val + H) H) := by
      constructor
      · intro hinj r s hrs
        apply hinj
        funext w
        let c : S := ⟨-value u v (flatten w.val.val), by
          change -value u v (flatten w.val.val) ∈ centers t H u v available
          exact Finset.mem_image.mpr ⟨w.val, w.property, rfl⟩⟩
        exact congrFun hrs c
      · intro hinj r s hrs
        apply hinj
        funext c
        obtain ⟨w, hw, hcw⟩ := Finset.mem_image.mp c.property
        let w' : ↑available := ⟨w, hw⟩
        have heq := congrFun hrs w'
        change Nat.gcd ((r - (-value u v (flatten w.val))).val + H) H =
          Nat.gcd ((s - (-value u v (flatten w.val))).val + H) H at heq
        simpa only [show c.val = -value u v (flatten w.val) from hcw.symm] using heq
    rw [probe_actual_ident_iff_model H t hH u v hrow available, hmodel,
      probe_global_crt_injective H hH S]
    unfold BottomBlocks
    constructor
    · intro h p
      have hp : p.val.Prime := Nat.prime_of_mem_primeFactors p.property
      letI : Fact p.val.Prime := ⟨hp⟩
      have he : 1 ≤ H.factorization p.val :=
        hp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors p.property)
      have hs := (probe_local_criterion p.val (H.factorization p.val) he
        (S.image fun c : ZMod H =>
          (ZMod.cast c : ZMod (p.val ^ H.factorization p.val)))).2 (h p)
      simpa only [localCenters, S] using hs
    · intro h p
      have hp : p.val.Prime := Nat.prime_of_mem_primeFactors p.property
      letI : Fact p.val.Prime := ⟨hp⟩
      have he : 1 ≤ H.factorization p.val :=
        hp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors p.property)
      apply (probe_local_criterion p.val (H.factorization p.val) he
        (S.image fun c : ZMod H =>
          (ZMod.cast c : ZMod (p.val ^ H.factorization p.val)))).1
      simpa only [localCenters, S] using h p

  have probe_count (H t : Nat) (hH : 2 ≤ H) (u v : ZMod H)
      (hblocks : BottomBlocks t H u v (Finset.univ : Finset (SuccessfulWord t))) :
      ∀ p : H.primeFactors,
        p.val ^ (H.factorization p.val - 1) * (p.val - 1) ≤
          Nat.fib (3 * t + 1) := by
    classical
    intro p
    let e := H.factorization p.val
    let X := ZMod (p.val ^ e)
    let Y := ZMod (p.val ^ (e-1))
    let π := primePowerProjection p.val (Nat.sub_le e 1)
    let S : Finset X := localCenters t H u v Finset.univ p
    have hp : p.val.Prime := Nat.prime_of_mem_primeFactors p.property
    letI : Fact p.val.Prime := ⟨hp⟩
    have he : 1 ≤ e :=
      hp.factorization_pos_of_dvd (by omega) (Nat.dvd_of_mem_primeFactors p.property)
    have hcard : (p.val-1) * p.val ^ (e-1) ≤ S.card := by
      have hr := D5.S3.Observer.Budget.PrimePowerNonadaptiveResolution.result
        p.val e he
      rcases hr with ⟨_,_,_,_,_,_,fibers,criterion,_,_⟩
      have inj : Set.InjOn π (Sᶜ : Finset X) := by
        intro a ha b hb hab
        have hcompl (r : Y) : (Sᶜ.filter fun a => π a = r).card ≤ 1 := by
          have hpart := Finset.card_filter_add_card_filter_not
            (s := Finset.univ.filter fun a : X => π a = r)
            (p := fun a => a ∈ S)
          have hfirst : ((Finset.univ.filter fun a : X => π a = r).filter
              fun a => a ∈ S) = S.filter (fun a => π a = r) := by
            ext a; simp [and_comm]
          have hsecond : ((Finset.univ.filter fun a : X => π a = r).filter
              fun a => ¬a ∈ S) = Sᶜ.filter (fun a => π a = r) := by
            ext a; simp [and_comm]
          rw [hfirst,hsecond] at hpart
          have hfib : (S.filter fun a => π a = r).card +
              (Sᶜ.filter fun a => π a = r).card = p.val := hpart.trans (fibers r)
          have hs := hblocks p r
          change (S.filter fun a => π a = r).card ≥ p.val - 1 at hs
          omega
        exact Finset.card_le_one.mp (hcompl (π a)) a
          (Finset.mem_filter.mpr ⟨ha, rfl⟩) b
          (Finset.mem_filter.mpr ⟨hb, hab.symm⟩)
      have card := (Finset.card_image_of_injOn inj).symm.trans_le
        (Finset.card_le_univ (Sᶜ.image π))
      have total := S.card_add_card_compl
      rw [ZMod.card] at card total
      change Sᶜ.card ≤ p.val ^ (e - 1) at card
      change S.card + Sᶜ.card = p.val ^ e at total
      have hpow : p.val ^ e = p.val ^ (e-1) * p.val := by
        rw [← pow_succ, Nat.sub_add_cancel he]
      have total' : S.card + Sᶜ.card = p.val ^ (e-1) * p.val := total.trans hpow
      calc
        (p.val-1) * p.val ^ (e-1) = p.val * p.val ^ (e-1) - p.val ^ (e-1) := by
          rw [Nat.sub_mul, one_mul]
        _ = p.val ^ (e-1) * p.val - p.val ^ (e-1) := by
          rw [Nat.mul_comm p.val]
        _ ≤ S.card := by omega
    have hlocal : S.card ≤ (centers t H u v Finset.univ).card := by
      exact Finset.card_image_le
    have hglobal : (centers t H u v Finset.univ).card ≤
        Fintype.card (SuccessfulWord t) := by
      exact Finset.card_image_le.trans (by simp)
    have hcount := (LiteralWindowEnd.result t).2.1
    calc
      p.val ^ (e-1) * (p.val-1) = (p.val-1) * p.val ^ (e-1) := Nat.mul_comm _ _
      _ ≤ S.card := hcard
      _ ≤ (centers t H u v Finset.univ).card := hlocal
      _ ≤ Fintype.card (SuccessfulWord t) := hglobal
      _ = Nat.fib (3*t+1) := hcount
  have probe_quotient (H : Nat) (hH : 2 ≤ H) (x y : ActualPrefix) :
      CompleteFutureIndex H x y ↔ CompleteFuture H x y := by
    have hmap (source : ActualPrefix) (suffix : List Window) :
        rawIndex H source suffix = Option.map (fun d => H / d) (rawGcd H source suffix) := by
      unfold rawIndex rawGcd observe
      split_ifs <;> rfl
    have gcd_dvd (source : ActualPrefix) (suffix : List Window) (d : Nat)
        (hd : rawGcd H source suffix = some d) : d ∣ H := by
      unfold rawGcd observe at hd
      split_ifs at hd
      all_goals try cases hd
      all_goals exact Nat.gcd_dvd_right _ _
    have quotient_iff (a b : Nat) (ha : a ∣ H) (hb : b ∣ H) :
        H / a = H / b ↔ a = b := by
      constructor
      · intro heq
        have hz := Nat.mul_div_cancel' ha
        have hv := Nat.mul_div_cancel' hb
        rw [← heq] at hv
        have hpos : 0 < H / a := Nat.div_pos
          (Nat.le_of_dvd (by omega) ha)
          (Nat.pos_of_ne_zero (by
            intro hz0
            rw [hz0] at ha
            exact (by omega : H ≠ 0) (by simpa using ha)))
        exact Nat.eq_of_mul_eq_mul_right hpos (hz.trans hv.symm)
      · intro heq; rw [heq]
    constructor
    · intro hi suffix
      have heq := hi suffix
      rw [hmap x suffix, hmap y suffix] at heq
      cases hx : rawGcd H x suffix with
      | none =>
        cases hy : rawGcd H y suffix with
        | none => simp [hx, hy]
        | some b => simp [hx, hy] at heq
      | some a =>
        cases hy : rawGcd H y suffix with
        | none => simp [hx, hy] at heq
        | some b =>
          simp [hx, hy] at heq
          have hab := (quotient_iff a b (gcd_dvd x suffix a hx)
            (gcd_dvd y suffix b hy)).mp heq
          simpa [hx, hy, hab]
    · intro hg suffix
      rw [hmap x suffix, hmap y suffix, hg suffix]

  unfold Target
  refine ⟨actual_common_depth_fullness H hH u v hrow, ?_,
    actual_future_residue_equivalence H hH u v hrow, ?_, ?_, ?_, actual_nonconverse⟩
  · intro source
    have hinit : initialized source.epsilon source.past =
        some (sourceNumber source) := by
      unfold initialized observe sourceNumber
      rw [source.terminal]
      rfl
    exact (LiteralWindowEnd.result 0).2.2.2.2.2.2.2
      source.epsilon source.past (sourceNumber source) hinit
  · intro x y
    exact probe_quotient H hH x.val y.val
  · intro available
    exact probe_complete_criterion H t hH u v hrow available
  · exact probe_count H t hH u v

#print axioms result

end D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockResolution
