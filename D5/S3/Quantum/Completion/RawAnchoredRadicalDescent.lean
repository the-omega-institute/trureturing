/- GID: D5/S3/Quantum/Completion/RawAnchoredRadicalDescent
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/RawAnchoredRadicalDescent
   mirror-E: none(waiver:unbounded-original-domain-descent)
   anchors: []
   utility: none
   digest: The raw C133-V balance yields the anchored free comparison form, its two-sided radical quotient, and the exact marker transport identities.
-/

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Tactic
import D5.S3.Quantum.Completion.RawThreePhaseDescent

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Completion.RawAnchoredRadicalDescent

open D5.S3.Quantum.Completion.RawThreePhaseDescent

abbrev E (M : Type*) := M →₀ ℝ

def e {M : Type*} [MulOneClass M] (a : M) : E M :=
  Finsupp.single a 1 - Finsupp.single 1 1

def q {M : Type*} [MulOneClass M] (c : M → M → ℝ) (a : M) : ℝ := c a 1

def r {M : Type*} [MulOneClass M] (c : M → M → ℝ) (b : M) : ℝ := c 1 b

def kernel {M : Type*} [MulOneClass M] (c : M → M → ℝ) (a b : M) : ℝ :=
  (q c a + r c b - c a b) / 2

def anchoredForm {M : Type*} [MulOneClass M] (c : M → M → ℝ) :
    E M →ₗ[ℝ] E M →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ
    (fun a : M => Finsupp.linearCombination ℝ (fun b : M => kernel c a b))

private theorem e_one {M : Type*} [MulOneClass M] : e (1 : M) = 0 := by
  simp [e]

private theorem anchoredForm_e {M : Type*} [MulOneClass M] (c : M → M → ℝ)
    (h11 : c 1 1 = 0) (a b : M) :
    anchoredForm c (e a) (e b) = kernel c a b := by
  simp [anchoredForm, e, kernel, q, r, sub_eq_add_neg, add_assoc, add_left_comm,
    add_comm, h11]

def leftRadical {M : Type*} [MulOneClass M] (c : M → M → ℝ) : Submodule ℝ (E M) :=
  { carrier := {x | ∀ y, anchoredForm c x y = 0}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy z
      rw [(anchoredForm c).map_add]
      rw [LinearMap.add_apply, hx z, hy z, add_zero]
    smul_mem' := by
      intro a x hx y
      rw [(anchoredForm c).map_smul]
      rw [LinearMap.smul_apply, hx y, smul_zero] }

def rightRadical {M : Type*} [MulOneClass M] (c : M → M → ℝ) : Submodule ℝ (E M) :=
  { carrier := {y | ∀ x, anchoredForm c x y = 0}
    zero_mem' := by simp
    add_mem' := by
      intro x y hx hy z
      rw [((anchoredForm c) z).map_add]
      rw [hx z, hy z, add_zero]
    smul_mem' := by
      intro a x hx y
      rw [((anchoredForm c) y).map_smul]
      rw [hx y, smul_zero] }

def radical {M : Type*} [MulOneClass M] (c : M → M → ℝ) : Submodule ℝ (E M) :=
  leftRadical c ⊓ rightRadical c

abbrev V {M : Type*} [MulOneClass M] (c : M → M → ℝ) :=
  E M ⧸ radical c

def beta {M : Type*} [MulOneClass M] (c : M → M → ℝ) (a : M) : V c :=
  (radical c).mkQ (e a)

private theorem beta_one {M : Type*} [MulOneClass M] (c : M → M → ℝ) : beta c 1 = 0 := by
  simp [beta, e]

private theorem radical_left {M : Type*} [MulOneClass M] (c : M → M → ℝ)
    {x : E M} (hx : x ∈ radical c) : ∀ y, anchoredForm c x y = 0 := by
  exact hx.1

private theorem radical_right {M : Type*} [MulOneClass M] (c : M → M → ℝ)
    {y : E M} (hy : y ∈ radical c) : ∀ x, anchoredForm c x y = 0 := by
  exact hy.2

def quotientForm {M : Type*} [MulOneClass M] (c : M → M → ℝ) :
    V c →ₗ[ℝ] V c →ₗ[ℝ] ℝ := by
  apply LinearMap.liftQ₂ (radical c) (radical c) (anchoredForm c)
  · intro x hx
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro y
    exact radical_left c hx y
  · intro y hy
    rw [LinearMap.mem_ker]
    apply LinearMap.ext
    intro x
    exact radical_right c hy x

private theorem quotientForm_beta {M : Type*} [MulOneClass M] (c : M → M → ℝ)
    (h11 : c 1 1 = 0) (a b : M) :
    quotientForm c (beta c a) (beta c b) = kernel c a b := by
  change (LinearMap.liftQ₂ (radical c) (radical c) (anchoredForm c) _ _)
      ((radical c).mkQ (e a)) ((radical c).mkQ (e b)) = _
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, LinearMap.liftQ₂_mk]
  exact anchoredForm_e c h11 a b

def markerLinear {M : Type*} [MulOneClass M] (U : M → M) : E M →ₗ[ℝ] E M :=
  Finsupp.lmapDomain ℝ ℝ U

private theorem kernel_marker_invariant {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M) :
    kernel c (U a) (U b) = kernel c a b := by
  have hm := (raw_marker_readouts U c h).1
  have hqa : c (U a) 1 = c a 1 := by
    simpa [h.marker_one] using hm a 1
  have hrb : c 1 (U b) = c 1 b := by
    simpa [h.marker_one] using hm 1 b
  have hab : c (U a) (U b) = c a b := hm a b
  simp only [kernel, q, r]
  rw [hqa, hrb, hab]

private theorem markerForm_invariant {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x y : E M) :
    anchoredForm c (markerLinear U x) (markerLinear U y) = anchoredForm c x y := by
  let I : M → E M →ₗ[ℝ] ℝ := fun a =>
    Finsupp.linearCombination ℝ (fun b : M => kernel c a b)
  have hi (a : M) : (I (U a)).comp (markerLinear U) = I a := by
    change (Finsupp.linearCombination ℝ (fun b : M => kernel c (U a) b)).comp
      (Finsupp.lmapDomain ℝ ℝ U) = _
    rw [Finsupp.linearCombination_comp_lmapDomain]
    change Finsupp.linearCombination ℝ (fun b : M => kernel c (U a) (U b)) = _
    congr 1
    funext b
    exact kernel_marker_invariant U c h a b
  have ho : (anchoredForm c).comp (markerLinear U) =
      Finsupp.linearCombination ℝ (fun a : M => I (U a)) := by
    simpa [anchoredForm, I, markerLinear, Function.comp_def] using
      (Finsupp.linearCombination_comp_lmapDomain (R := ℝ) (v' := fun a : M => I a) U)
  calc
    anchoredForm c (markerLinear U x) (markerLinear U y) =
        (Finsupp.linearCombination ℝ (fun a : M => I (U a)) x)
          (markerLinear U y) := by rw [← ho]; rfl
    _ = (Finsupp.linearCombination ℝ (fun a : M => (I (U a)).comp (markerLinear U)) x) y := by
      simp [Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.comp_apply]
    _ = (Finsupp.linearCombination ℝ (fun a : M => I a) x) y := by
      simp_rw [hi]
    _ = anchoredForm c x y := by rfl

private theorem form_single_single {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (i j : M) (a b : ℝ) :
    anchoredForm c (Finsupp.single i a) (Finsupp.single j b) =
      a * b * kernel c i j := by
  simp [anchoredForm, Finsupp.linearCombination_apply, kernel]
  ring_nf

private theorem form_right_single_of_kernel {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (f : M → M)
    (hk : ∀ a b, kernel c a (f b) = kernel c a b)
    (x : E M) (a : M) (b : ℝ) :
    anchoredForm c x (Finsupp.single (f a) b) =
      anchoredForm c x (Finsupp.single a b) := by
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add i d x hi hd ih =>
      rw [(anchoredForm c).map_add]
      simp only [LinearMap.add_apply]
      rw [ih]
      simp only [form_single_single]
      rw [hk i a]

private theorem form_right_map_of_kernel {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (f : M → M)
    (hk : ∀ a b, kernel c a (f b) = kernel c a b)
    (x y : E M) :
    anchoredForm c x (Finsupp.lmapDomain ℝ ℝ f y) = anchoredForm c x y := by
  induction y using Finsupp.induction with
  | zero => simp
  | @single_add a b y ha hb ih =>
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_add]
      have haddL := (anchoredForm c x).map_add
        (Finsupp.mapDomain f (Finsupp.single a b)) (Finsupp.mapDomain f y)
      have haddR := (anchoredForm c x).map_add (Finsupp.single a b) y
      have ih' : anchoredForm c x (Finsupp.mapDomain f y) = anchoredForm c x y := by
        simpa [Finsupp.lmapDomain_apply] using ih
      rw [haddL, haddR, ih', Finsupp.mapDomain_single]
      exact congrArg (fun t => t + anchoredForm c x y)
        (form_right_single_of_kernel c f hk x a b)

private theorem form_left_single_of_kernel {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (f : M → M)
    (hk : ∀ a b, kernel c (f a) b = kernel c a b)
    (y : E M) (a : M) (b : ℝ) :
    anchoredForm c (Finsupp.single (f a) b) y =
      anchoredForm c (Finsupp.single a b) y := by
  induction y using Finsupp.induction with
  | zero => simp
  | @single_add j d y hj hd ih =>
      rw [((anchoredForm c) (Finsupp.single (f a) b)).map_add,
        ((anchoredForm c) (Finsupp.single a b)).map_add, ih]
      simp only [form_single_single]
      rw [hk a j]

private theorem form_left_map_of_kernel {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (f : M → M)
    (hk : ∀ a b, kernel c (f a) b = kernel c a b)
    (x y : E M) :
    anchoredForm c (Finsupp.lmapDomain ℝ ℝ f x) y = anchoredForm c x y := by
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add a b x ha hb ih =>
      rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_add]
      have haddL := (anchoredForm c).map_add
        (Finsupp.mapDomain f (Finsupp.single a b)) (Finsupp.mapDomain f x)
      have haddR := (anchoredForm c).map_add (Finsupp.single a b) x
      have ih' : anchoredForm c (Finsupp.mapDomain f x) y = anchoredForm c x y := by
        simpa [Finsupp.lmapDomain_apply] using ih
      rw [haddL, haddR, LinearMap.add_apply, ih', Finsupp.mapDomain_single]
      exact congrArg (fun t => t + anchoredForm c x y)
        (form_left_single_of_kernel c f hk y a b)

private theorem marker_beta_transport {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) :
    beta c (U a) = (radical c).mkQ (markerLinear U (e a)) := by
  change (radical c).mkQ (e (U a)) = (radical c).mkQ (markerLinear U (e a))
  congr 1
  simp only [markerLinear, e, Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub,
    Finsupp.mapDomain_single]
  rw [h.marker_one]

private theorem kernel_marker_period_three_left {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M) :
    kernel c (U (U (U a))) b = kernel c a b := by
  have hr := (raw_marker_readouts U c h).2.2 a b
  have hq := (raw_marker_readouts U c h).2.2 a 1
  simp only [kernel, q, r]
  rw [hq.1, hr.1]

private theorem kernel_marker_period_three_right {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M) :
    kernel c a (U (U (U b))) = kernel c a b := by
  have hr := (raw_marker_readouts U c h).2.2 b a
  have hq := (raw_marker_readouts U c h).2.2 b 1
  simp only [kernel, q, r]
  rw [hq.2, hr.2]

private theorem marker_period_three_on_beta {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) :
    beta c (U (U (U a))) = beta c a := by
  let f : M → M := fun x => U (U (U x))
  have hf1 : f 1 = 1 := by simp [f, h.marker_one]
  have hleft : ∀ y : E M, anchoredForm c (e (f a) - e a) y = 0 := by
    intro y
    have hmap := form_left_map_of_kernel c f
      (fun x z => kernel_marker_period_three_left U c h x z) (e a) y
    have he : markerLinear f (e a) = e (f a) := by
      simp only [markerLinear, e, Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub,
        Finsupp.mapDomain_single]
      rw [hf1]
    have hmap' : anchoredForm c (markerLinear f (e a)) y = anchoredForm c (e a) y := by
      simpa [markerLinear] using hmap
    rw [← he, (anchoredForm c).map_sub, LinearMap.sub_apply, hmap']
    exact sub_self _
  have hright : ∀ x : E M, anchoredForm c x (e (f a) - e a) = 0 := by
    intro x
    have hmap := form_right_map_of_kernel c f
      (fun z y => kernel_marker_period_three_right U c h z y) x (e a)
    have he : markerLinear f (e a) = e (f a) := by
      simp only [markerLinear, e, Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub,
        Finsupp.mapDomain_single]
      rw [hf1]
    have hmap' : anchoredForm c x (markerLinear f (e a)) = anchoredForm c x (e a) := by
      simpa [markerLinear] using hmap
    rw [← he, ((anchoredForm c) x).map_sub, hmap']
    exact sub_self _
  apply (Submodule.Quotient.eq (radical c)).2
  exact ⟨hleft, hright⟩

private theorem marker_radical_stable {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    {x : E M} (hx : x ∈ radical c) : markerLinear U x ∈ radical c := by
  let f : M → M := fun a => U (U (U a))
  have hcomp : markerLinear f =
      (markerLinear U).comp ((markerLinear U).comp (markerLinear U)) := by
    change Finsupp.lmapDomain ℝ ℝ f =
      (Finsupp.lmapDomain ℝ ℝ U).comp
        ((Finsupp.lmapDomain ℝ ℝ U).comp (Finsupp.lmapDomain ℝ ℝ U))
    rw [show f = U ∘ (U ∘ U) by funext z; rfl,
      Finsupp.lmapDomain_comp, Finsupp.lmapDomain_comp]
  have hleft (y : E M) : anchoredForm c (markerLinear U x) y = 0 := by
    have hp := form_right_map_of_kernel c f
      (fun a b => kernel_marker_period_three_right U c h a b)
      (markerLinear U x) y
    have hm := markerForm_invariant U c h x
      (markerLinear U (markerLinear U y))
    have hz := radical_left c hx (markerLinear U (markerLinear U y))
    calc
      anchoredForm c (markerLinear U x) y =
          anchoredForm c (markerLinear U x) (markerLinear f y) := hp.symm
      _ = anchoredForm c (markerLinear U x)
          (markerLinear U (markerLinear U (markerLinear U y))) := by
            rw [hcomp]
            rfl
      _ = anchoredForm c x (markerLinear U (markerLinear U y)) := hm
      _ = 0 := hz
  have hright (y : E M) : anchoredForm c y (markerLinear U x) = 0 := by
    have hp := form_left_map_of_kernel c f
      (fun a b => kernel_marker_period_three_left U c h a b) y
      (markerLinear U x)
    have hm := markerForm_invariant U c h
      (markerLinear U (markerLinear U y)) x
    have hz := radical_right c hx (markerLinear U (markerLinear U y))
    calc
      anchoredForm c y (markerLinear U x) =
          anchoredForm c (markerLinear f y) (markerLinear U x) := hp.symm
      _ = anchoredForm c
          (markerLinear U (markerLinear U (markerLinear U y)))
          (markerLinear U x) := by
            rw [hcomp]
            rfl
      _ = anchoredForm c (markerLinear U (markerLinear U y)) x := hm
      _ = 0 := hz
  exact ⟨hleft, hright⟩

def markerQuotient {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) : V c →ₗ[ℝ] V c :=
  (radical c).mapQ (radical c) (markerLinear U) (by
    intro x hx
    exact marker_radical_stable U c h hx)

private theorem markerQuotient_beta {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) :
    markerQuotient U c h (beta c a) = beta c (U a) := by
  change markerQuotient U c h ((radical c).mkQ (e a)) =
    (radical c).mkQ (e (U a))
  rw [markerQuotient, Submodule.mkQ_apply, Submodule.mapQ_apply,
    Submodule.mkQ_apply]
  congr 1
  simp only [markerLinear, e, Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub,
    Finsupp.mapDomain_single]
  rw [h.marker_one]

private theorem markerQuotient_three_beta {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) :
    markerQuotient U c h
        (markerQuotient U c h (markerQuotient U c h (beta c a))) = beta c a := by
  rw [markerQuotient_beta, markerQuotient_beta, markerQuotient_beta,
    marker_period_three_on_beta U c h]

private theorem quotientForm_marker_beta_invariant {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M)
    (h11 : c 1 1 = 0) :
    quotientForm c (markerQuotient U c h (beta c a))
        (markerQuotient U c h (beta c b)) =
      quotientForm c (beta c a) (beta c b) := by
  rw [markerQuotient_beta, markerQuotient_beta,
    quotientForm_beta c h11, quotientForm_beta c h11,
    kernel_marker_invariant U c h]

def defect {M : Type*} [MulOneClass M] (c : M → M → ℝ) (a u : M) : V c :=
  beta c (a * u) - beta c a - beta c u

private theorem defect_one_left {M : Type*} [MulOneClass M] (c : M → M → ℝ) (u : M) :
    defect c 1 u = 0 := by
  simp [defect, beta_one]

private theorem defect_one_right {M : Type*} [MulOneClass M] (c : M → M → ℝ) (a : M) :
    defect c a 1 = 0 := by
  simp [defect, beta_one]

theorem raw_anchored_radical_descent {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    c 1 1 = 0 ∧
      beta c 1 = 0 ∧
      (∀ a b, quotientForm c (beta c a) (beta c b) = kernel c a b) ∧
      (∀ x y, anchoredForm c (markerLinear U x) (markerLinear U y) =
        anchoredForm c x y) ∧
      (∀ a, beta c (U (U (U a))) = beta c a) ∧
      (∀ x, x ∈ radical c → markerLinear U x ∈ radical c) ∧
      (∀ a, markerQuotient U c h (beta c a) = beta c (U a)) ∧
      (∀ a, markerQuotient U c h
        (markerQuotient U c h (markerQuotient U c h (beta c a))) = beta c a) ∧
      (∀ a, defect c 1 a = 0) ∧
      (∀ a, defect c a 1 = 0) := by
  refine ⟨h.diagonal 1, beta_one c, ?_, markerForm_invariant U c h,
    marker_period_three_on_beta U c h, (fun x hx => marker_radical_stable U c h hx),
    ?_, ?_, defect_one_left c, defect_one_right c⟩
  · intro a b
    exact quotientForm_beta c (h.diagonal 1) a b
  · exact markerQuotient_beta U c h
  · exact markerQuotient_three_beta U c h

end D5.S3.Quantum.Completion.RawAnchoredRadicalDescent
