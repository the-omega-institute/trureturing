/- GID: D5/S3/Quantum/Completion/RawAnchoredRadicalDescent
   generality: G
   mirror-B: D5/B/S3/Quantum/Completion/RawAnchoredRadicalDescent
   mirror-E: none(waiver:unbounded-original-domain-descent)
   anchors: []
   utility: none
   digest: Raw balance yields the actual Fourier defect quotient and additive marker descent. -/

import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Quotient.Bilinear
import Mathlib.Tactic
import D5.S3.Quantum.Completion.RawThreePhaseDescent
import D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity

/-! Anchored comparison forms, ordered Fourier constraints and the actual defect quotient.
The construction retains the original unital magma and both pairing orders. -/

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
  simp [anchoredForm, e, kernel, q, r, sub_eq_add_neg, add_comm, h11]

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
  simp [beta, e_one]

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
      simp [Finsupp.linearCombination_apply, Finsupp.sum]
    _ = (Finsupp.linearCombination ℝ (fun a : M => I a) x) y := by
      simp_rw [hi]
    _ = anchoredForm c x y := by rfl

private theorem form_single_single {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (i j : M) (a b : ℝ) :
    anchoredForm c (Finsupp.single i a) (Finsupp.single j b) =
      a * b * kernel c i j := by
  simp [anchoredForm, Finsupp.linearCombination_apply, kernel]
  ring_nf

/-- The source's anchored free carrier, inside the full finite-support carrier. -/
def anchoredSpan (M : Type*) [MulOneClass M] : Submodule ℝ (E M) :=
  Submodule.span ℝ (Set.range (e : M → E M))

private theorem single_one_radical {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (h11 : c 1 1 = 0) :
    Finsupp.single (1 : M) (1 : ℝ) ∈ radical c := by
  constructor
  · intro y
    induction y using Finsupp.induction with
    | zero => simp
    | @single_add a b y ha hb ih =>
        rw [map_add, ih, add_zero, form_single_single]
        simp [kernel, q, r, h11]
  · intro x
    induction x using Finsupp.induction with
    | zero => simp
    | @single_add a b x ha hb ih =>
        rw [map_add, LinearMap.add_apply, ih, add_zero, form_single_single]
        simp [kernel, q, r, h11]

private theorem mkQ_single {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (h11 : c 1 1 = 0) (a : M) (t : ℝ) :
    (radical c).mkQ (Finsupp.single a t) = t • beta c a := by
  have hz : (radical c).mkQ (Finsupp.single (1 : M) (1 : ℝ)) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (single_one_radical c h11)
  have he : Finsupp.single a t = t • e a + t • Finsupp.single (1 : M) (1 : ℝ) := by
    simp [e, smul_sub]
  rw [he, map_add, map_smul, map_smul, hz, smul_zero, add_zero]
  rfl

private theorem anchoredSpan_quotient {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (h11 : c 1 1 = 0) :
    Submodule.map (radical c).mkQ (anchoredSpan M) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨x, rfl⟩ := (radical c).mkQ_surjective z
  induction x using Finsupp.induction with
  | zero => simp
  | @single_add a t x ha ht ih =>
      rw [map_add, mkQ_single c h11]
      exact Submodule.add_mem _
        (Submodule.smul_mem _ t
          ⟨e a, Submodule.subset_span (Set.mem_range_self a), rfl⟩) (ih trivial)

private theorem beta_span {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (h11 : c 1 1 = 0) :
    Submodule.span ℝ (Set.range (beta c)) = ⊤ := by
  have he : Submodule.map (radical c).mkQ (anchoredSpan M) =
      Submodule.span ℝ (Set.range (beta c)) := by
    rw [anchoredSpan, Submodule.map_span]
    congr 1
    ext z
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨e a, Set.mem_range_self a, rfl⟩
  rw [← he]
  exact anchoredSpan_quotient c h11

private theorem beta_induction {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (h11 : c 1 1 = 0) {P : V c → Prop}
    (hz : P 0) (hb : ∀ a, P (beta c a))
    (ha : ∀ x y, P x → P y → P (x + y))
    (hs : ∀ (t : ℝ) x, P x → P (t • x)) (x : V c) : P x := by
  have hx : x ∈ Submodule.span ℝ (Set.range (beta c)) := by rw [beta_span c h11]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => rcases hy with ⟨a, rfl⟩; exact hb a
  | zero => exact hz
  | add x y _ _ hx hy => exact ha x y hx hy
  | smul t x _ hx => exact hs t x hx

private theorem quotient_joint_nondegenerate {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (h11 : c 1 1 = 0) (z : V c)
    (hl : ∀ a, quotientForm c z (beta c a) = 0)
    (hr : ∀ a, quotientForm c (beta c a) z = 0) : z = 0 := by
  have hleft (y : V c) : quotientForm c z y = 0 := by
    exact beta_induction c h11 (P := fun y => quotientForm c z y = 0) (by simp) hl
      (by intro x y hx hy; simp [map_add, hx, hy])
      (by intro t x hx; simp [map_smul, hx]) y
  have hright (x : V c) : quotientForm c x z = 0 := by
    exact beta_induction c h11 (P := fun x => quotientForm c x z = 0) (by simp) hr
      (by intro x y hx hy; simp [map_add, hx, hy])
      (by intro t x hx; simp [map_smul, hx]) x
  obtain ⟨x, rfl⟩ := (radical c).mkQ_surjective z
  apply (Submodule.Quotient.mk_eq_zero _).2
  exact ⟨fun y => hleft ((radical c).mkQ y), fun y => hright ((radical c).mkQ y)⟩

private theorem beta_ext {M F : Type*} [MulOneClass M] [AddCommGroup F] [Module ℝ F]
    (c : M → M → ℝ) (h11 : c 1 1 = 0) (f g : V c →ₗ[ℝ] F)
    (hb : ∀ a, f (beta c a) = g (beta c a)) : f = g := by
  apply LinearMap.ext
  intro x
  exact beta_induction c h11 (P := fun x => f x = g x) (by simp) hb
    (by intro x y hx hy; simp [map_add, hx, hy])
    (by intro t x hx; simp [map_smul, hx]) x

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

private theorem markerQuotient_three {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : V c) :
    markerQuotient U c h (markerQuotient U c h (markerQuotient U c h x)) = x := by
  have he : (markerQuotient U c h).comp
      ((markerQuotient U c h).comp (markerQuotient U c h)) = LinearMap.id := by
    apply beta_ext c (h.diagonal 1)
    intro a
    exact markerQuotient_three_beta U c h a
  exact LinearMap.congr_fun he x

private theorem quotientForm_marker_invariant {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x y : V c) :
    quotientForm c (markerQuotient U c h x) (markerQuotient U c h y) =
      quotientForm c x y := by
  apply beta_induction c (h.diagonal 1) (P := fun x => ∀ y,
    quotientForm c (markerQuotient U c h x) (markerQuotient U c h y) = quotientForm c x y)
    (by simp) ?_ ?_ ?_ x y
  · intro a y
    exact beta_induction c (h.diagonal 1) (P := fun y =>
      quotientForm c (markerQuotient U c h (beta c a)) (markerQuotient U c h y) =
        quotientForm c (beta c a) y) (by simp)
      (fun b => quotientForm_marker_beta_invariant U c h a b (h.diagonal 1))
      (by intro x y hx hy; simp [map_add, hx, hy])
      (by intro t x hx; simp [map_smul, hx]) y
  · intro x y hx hy z
    simp [map_add, hx z, hy z]
  · intro t x hx y
    simp [map_smul, hx y]

private theorem q_average {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a u : M) :
    q c (a * u) + q c (a * U u) + q c (a * U (U u)) =
      3 * q c a + 3 * q c u := by
  simpa [q, h.marker_one] using h.balance a 1 u 1

private theorem r_average {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (b v : M) :
    r c (b * v) + r c (b * U v) + r c (b * U (U v)) =
      3 * r c b + 3 * r c v := by
  simpa [r, h.marker_one] using h.balance 1 b 1 v

private theorem quotient_bilinear_balance {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b u v : M) :
    quotientForm c (beta c (a * u)) (beta c (b * v)) +
      quotientForm c (beta c (a * U u)) (beta c (b * U v)) +
      quotientForm c (beta c (a * U (U u))) (beta c (b * U (U v))) =
      3 * quotientForm c (beta c a) (beta c b) +
      3 * quotientForm c (beta c u) (beta c v) := by
  simp only [quotientForm_beta c (h.diagonal 1), kernel]
  have hq := q_average U c h a u
  have hr := r_average U c h b v
  have hc := h.balance a b u v
  linarith

private theorem difference_diagonal {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M) :
    quotientForm c (beta c a - beta c b) (beta c a - beta c b) =
      (c a b + c b a) / 2 := by
  simp only [map_sub, LinearMap.sub_apply, quotientForm_beta c (h.diagonal 1),
    kernel, h.diagonal]
  ring

private theorem unweighted_sum {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a u : M) :
    beta c (a * u) + beta c (a * U u) + beta c (a * U (U u)) =
      (3 : ℝ) • beta c a := by
  apply sub_eq_zero.mp
  apply quotient_joint_nondegenerate c (h.diagonal 1)
  · intro b
    have hb := quotient_bilinear_balance U c h a b u 1
    simp only [h.marker_one, mul_one, beta_one, map_zero, mul_zero, add_zero] at hb
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    linarith
  · intro b
    have hb := quotient_bilinear_balance U c h b a 1 u
    simp only [h.marker_one, mul_one, beta_one, map_zero, LinearMap.zero_apply,
      mul_zero, add_zero] at hb
    simp only [map_sub, map_add, map_smul, smul_eq_mul]
    linarith

private theorem marker_cyclotomic {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : V c) :
    x + markerQuotient U c h x +
      markerQuotient U c h (markerQuotient U c h x) = 0 := by
  have he : LinearMap.id + markerQuotient U c h +
      (markerQuotient U c h).comp (markerQuotient U c h) = 0 := by
    apply beta_ext c (h.diagonal 1)
    intro a
    simpa [LinearMap.add_apply, LinearMap.comp_apply, markerQuotient_beta,
      beta_one] using unweighted_sum U c h 1 a
  exact LinearMap.congr_fun he x

private theorem form_move_marker_left {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x y : V c) :
    quotientForm c (markerQuotient U c h x) y =
      quotientForm c x (markerQuotient U c h (markerQuotient U c h y)) := by
  simpa only [markerQuotient_three] using
    quotientForm_marker_invariant U c h x (markerQuotient U c h
      (markerQuotient U c h y))

private theorem form_move_marker_right {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x y : V c) :
    quotientForm c x (markerQuotient U c h y) =
      quotientForm c (markerQuotient U c h (markerQuotient U c h x)) y := by
  simpa only [markerQuotient_three] using
    quotientForm_marker_invariant U c h (markerQuotient U c h
      (markerQuotient U c h x)) y

private theorem inverse_weighted_sum {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a u : M) :
    beta c (a * u) +
      markerQuotient U c h (markerQuotient U c h (beta c (a * U u))) +
      markerQuotient U c h (beta c (a * U (U u))) = (3 : ℝ) • beta c u := by
  apply sub_eq_zero.mp
  apply quotient_joint_nondegenerate c (h.diagonal 1)
  · intro v
    have hb := quotient_bilinear_balance U c h a 1 u v
    simp only [one_mul, beta_one, map_zero, mul_zero, zero_add] at hb
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply,
      LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    simp only [← markerQuotient_beta U c h] at hb
    rw [form_move_marker_right, ← form_move_marker_left] at hb
    linarith
  · intro v
    have hb := quotient_bilinear_balance U c h 1 a v u
    simp only [one_mul, beta_one, map_zero, LinearMap.zero_apply,
      mul_zero, zero_add] at hb
    simp only [map_sub, map_add, map_smul, smul_eq_mul]
    simp only [← markerQuotient_beta U c h] at hb
    rw [form_move_marker_left, ← form_move_marker_right] at hb
    linarith

def defect {M : Type*} [MulOneClass M] (c : M → M → ℝ) (a u : M) : V c :=
  beta c (a * u) - beta c a - beta c u

private theorem three_character_elimination {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (d₀ d₁ d₂ : V c)
    (hs : d₀ + d₁ + d₂ = 0)
    (hw : d₀ + markerQuotient U c h (markerQuotient U c h d₁) +
      markerQuotient U c h d₂ = 0) :
    d₁ = markerQuotient U c h (markerQuotient U c h d₀) ∧
      d₂ = markerQuotient U c h d₀ := by
  let R := markerQuotient U c h
  have hz : (3 : ℝ) • (d₁ - R (R d₀)) = 0 := by
    calc
      _ = R (d₀ + R (R d₁) + R d₂) -
          R (R (d₀ + R (R d₁) + R d₂)) - R (R (d₀ + d₁ + d₂)) +
          (d₀ + d₁ + d₂) - (d₀ + R d₀ + R (R d₀)) +
          (d₁ + R d₁ + R (R d₁)) := by
            simp only [map_add, markerQuotient_three, R]
            module
      _ = 0 := by
        rw [hw, hs, marker_cyclotomic U c h, marker_cyclotomic U c h]
        simp
  have hd₁ : d₁ = R (R d₀) :=
    sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  refine ⟨hd₁, ?_⟩
  have hc : d₀ + R (R d₀) + R d₀ = 0 := by
    simpa only [add_assoc, add_comm, add_left_comm] using marker_cyclotomic U c h d₀
  rw [hd₁] at hs
  exact add_left_cancel (hs.trans hc.symm)

private theorem defect_character_constraints {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a u : M) :
    (defect c a u + defect c a (U u) + defect c a (U (U u)) = 0) ∧
    (defect c a u +
      markerQuotient U c h (markerQuotient U c h (defect c a (U u))) +
      markerQuotient U c h (defect c a (U (U u))) = 0) := by
  let R := markerQuotient U c h
  constructor
  · calc
      _ = (beta c (a * u) + beta c (a * U u) + beta c (a * U (U u))) -
          (3 : ℝ) • beta c a - (beta c u + R (beta c u) + R (R (beta c u))) := by
            simp only [defect, markerQuotient_beta, R]
            module
      _ = 0 := by rw [unweighted_sum U c h, marker_cyclotomic U c h]; simp
  · calc
      _ = (beta c (a * u) + R (R (beta c (a * U u))) +
          R (beta c (a * U (U u)))) - (3 : ℝ) • beta c u -
          (beta c a + R (beta c a) + R (R (beta c a))) := by
            simp only [defect, map_sub, markerQuotient_beta, marker_period_three_on_beta U c h, R]
            module
      _ = 0 := by rw [inverse_weighted_sum U c h, marker_cyclotomic U c h]; simp

private theorem defect_phases {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a u : M) :
    defect c a (U u) =
        markerQuotient U c h (markerQuotient U c h (defect c a u)) ∧
      defect c a (U (U u)) = markerQuotient U c h (defect c a u) := by
  have hc := defect_character_constraints U c h a u
  exact three_character_elimination U c h _ _ _ hc.1 hc.2

private theorem phase_children {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a u : M) :
    beta c (a * U u) = beta c a + markerQuotient U c h (beta c u) +
        markerQuotient U c h (markerQuotient U c h (defect c a u)) ∧
      beta c (a * U (U u)) = beta c a +
        markerQuotient U c h (markerQuotient U c h (beta c u)) +
        markerQuotient U c h (defect c a u) := by
  have hc := defect_phases U c h a u
  constructor
  · calc
      _ = beta c a + beta c (U u) + defect c a (U u) := by unfold defect; abel
      _ = _ := by rw [hc.1, markerQuotient_beta]
  · calc
      _ = beta c a + beta c (U (U u)) + defect c a (U (U u)) := by
        unfold defect; abel
      _ = _ := by rw [hc.2, markerQuotient_beta, markerQuotient_beta]

private theorem bilinear_fourier_average {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (a b u v d f : V c) :
    quotientForm c (a + u + d) (b + v + f) +
      quotientForm c
        (a + markerQuotient U c h u + markerQuotient U c h (markerQuotient U c h d))
        (b + markerQuotient U c h v + markerQuotient U c h (markerQuotient U c h f)) +
      quotientForm c
        (a + markerQuotient U c h (markerQuotient U c h u) + markerQuotient U c h d)
        (b + markerQuotient U c h (markerQuotient U c h v) + markerQuotient U c h f) =
      3 * quotientForm c a b + 3 * quotientForm c u v + 3 * quotientForm c d f := by
  have hz (x y : V c) : quotientForm c x y +
      quotientForm c x (markerQuotient U c h y) +
      quotientForm c x (markerQuotient U c h (markerQuotient U c h y)) = 0 := by
    rw [← map_add, ← map_add, marker_cyclotomic U c h, map_zero]
  have hab := hz a v
  have haf := hz a f
  have hub := hz u b
  have huf := hz u f
  have hdb := hz d b
  have hdv := hz d v
  simp only [map_add, LinearMap.add_apply, form_move_marker_left,
    markerQuotient_three]
  linarith

private theorem cross_defect_isotropic {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b u v : M) :
    quotientForm c (defect c a u) (defect c b v) = 0 := by
  have hb := quotient_bilinear_balance U c h a b u v
  have hp := phase_children U c h a u
  have hq := phase_children U c h b v
  rw [hp.1, hp.2, hq.1, hq.2] at hb
  have h₀ (a u : M) : beta c (a * u) = beta c a + beta c u + defect c a u := by
    unfold defect
    abel
  rw [h₀ a u, h₀ b v] at hb
  rw [bilinear_fourier_average U c h] at hb
  linarith

/-- The span of defects of the original, bracketed binary products. -/
def W {M : Type*} [MulOneClass M] (c : M → M → ℝ) : Submodule ℝ (V c) :=
  Submodule.span ℝ (Set.range (fun p : M × M => defect c p.1 p.2))

private theorem defect_mem_W {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (a u : M) : defect c a u ∈ W c :=
  Submodule.subset_span (Set.mem_range_self (a, u))

private theorem W_isotropic {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (x y : V c) (hx : x ∈ W c) (hy : y ∈ W c) : quotientForm c x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨⟨a, u⟩, rfl⟩
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨⟨b, v⟩, rfl⟩
      exact cross_defect_isotropic U c h a b u v
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul t x _ hx => simp [map_smul, hx]
  | zero => simp
  | add x y _ _ hx hy => simp [map_add, hx, hy]
  | smul t x _ hx => simp [map_smul, hx]

private theorem W_marker_stable {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    {x : V c} (hx : x ∈ W c) : markerQuotient U c h x ∈ W c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨⟨a, u⟩, rfl⟩
    rw [← (defect_phases U c h a u).2]
    exact defect_mem_W c a (U (U u))
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (W c).add_mem hx hy
  | smul t x _ hx => simpa only [map_smul] using (W c).smul_mem t hx

private theorem W_marker_image {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    Submodule.map (markerQuotient U c h) (W c) = W c := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact W_marker_stable U c h hx
  · intro x hx
    exact ⟨markerQuotient U c h (markerQuotient U c h x),
      W_marker_stable U c h (W_marker_stable U c h hx), markerQuotient_three U c h x⟩

abbrev GammaSpace {M : Type*} [MulOneClass M] (c : M → M → ℝ) := V c ⧸ W c

/-- The additive image is constructed from the same original labels. -/
def gamma {M : Type*} [MulOneClass M] (c : M → M → ℝ) (a : M) : GammaSpace c :=
  (W c).mkQ (beta c a)

def rho {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    GammaSpace c →ₗ[ℝ] GammaSpace c :=
  (W c).mapQ (W c) (markerQuotient U c h) (by
    intro x hx
    rw [← W_marker_image U c h]
    exact ⟨x, hx, rfl⟩)

private theorem gamma_one {M : Type*} [MulOneClass M] (c : M → M → ℝ) :
    gamma c 1 = 0 := by simp [gamma, beta_one]

private theorem gamma_mul {M : Type*} [MulOneClass M]
    (c : M → M → ℝ) (a u : M) : gamma c (a * u) = gamma c a + gamma c u := by
  have hz : (W c).mkQ (defect c a u) = 0 :=
    (Submodule.Quotient.mk_eq_zero _).2 (defect_mem_W c a u)
  apply sub_eq_zero.mp
  simpa only [defect, map_sub, gamma, sub_sub, map_add] using hz

private theorem gamma_marker {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) :
    gamma c (U a) = rho U c h (gamma c a) := by
  change (W c).mkQ (beta c (U a)) = (W c).mkQ (markerQuotient U c h (beta c a))
  rw [markerQuotient_beta]

private theorem gamma_phase_product {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a u : M) (k : ℕ) :
    gamma c (a * U^[k] u) = gamma c a + (rho U c h)^[k] (gamma c u) := by
  rw [gamma_mul]
  congr 1
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', gamma_marker, ih]

private theorem gamma_fibre_zero_comparison {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M)
    (hab : gamma c a = gamma c b) : c a b = 0 ∧ c b a = 0 := by
  have hw : beta c a - beta c b ∈ W c := (Submodule.Quotient.eq _).1 hab
  have hz := W_isotropic U c h _ _ hw hw
  rw [difference_diagonal U c h a b] at hz
  constructor <;> linarith [h.nonneg a b, h.nonneg b a]

/-- The original raw law constructs the anchored Fourier defect quotient. -/
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
    (∀ a, defect c a 1 = 0) ∧
    Submodule.map (radical c).mkQ (anchoredSpan M) = ⊤ ∧
    Submodule.span ℝ (Set.range (beta c)) = ⊤ ∧
    (∀ z, (∀ a, quotientForm c z (beta c a) = 0) →
      (∀ a, quotientForm c (beta c a) z = 0) → z = 0) ∧
    (∀ x, markerQuotient U c h (markerQuotient U c h (markerQuotient U c h x)) = x) ∧
    (∀ x y, quotientForm c (markerQuotient U c h x) (markerQuotient U c h y) =
      quotientForm c x y) ∧
    (∀ a b, quotientForm c (beta c a - beta c b) (beta c a - beta c b) =
      (c a b + c b a) / 2) ∧
    (∀ a u, q c (a * u) + q c (a * U u) + q c (a * U (U u)) =
      3 * q c a + 3 * q c u) ∧
    (∀ b v, r c (b * v) + r c (b * U v) + r c (b * U (U v)) =
      3 * r c b + 3 * r c v) ∧
    (∀ a b u v, quotientForm c (beta c (a * u)) (beta c (b * v)) +
      quotientForm c (beta c (a * U u)) (beta c (b * U v)) +
      quotientForm c (beta c (a * U (U u))) (beta c (b * U (U v))) =
      3 * quotientForm c (beta c a) (beta c b) +
      3 * quotientForm c (beta c u) (beta c v)) ∧
    (∀ a u, beta c (a * u) + beta c (a * U u) + beta c (a * U (U u)) =
      (3 : ℝ) • beta c a) ∧
    (∀ a u, beta c (a * u) +
      markerQuotient U c h (markerQuotient U c h (beta c (a * U u))) +
      markerQuotient U c h (beta c (a * U (U u))) = (3 : ℝ) • beta c u) ∧
    (∀ x, x + markerQuotient U c h x +
      markerQuotient U c h (markerQuotient U c h x) = 0) ∧
    (∀ a u, beta c (a * U u) = beta c a + markerQuotient U c h (beta c u) +
      markerQuotient U c h (markerQuotient U c h (defect c a u)) ∧
      beta c (a * U (U u)) = beta c a +
      markerQuotient U c h (markerQuotient U c h (beta c u)) +
      markerQuotient U c h (defect c a u)) ∧
    (∀ a b u v, quotientForm c (defect c a u) (defect c b v) = 0) ∧
    (∀ x y, x ∈ W c → y ∈ W c → quotientForm c x y = 0) ∧
    Submodule.map (markerQuotient U c h) (W c) = W c ∧
    gamma c 1 = 0 ∧
    (∀ a u, gamma c (a * u) = gamma c a + gamma c u) ∧
    (∀ a, gamma c (U a) = rho U c h (gamma c a)) ∧
    (∀ a u k, gamma c (a * U^[k] u) =
      gamma c a + (rho U c h)^[k] (gamma c u)) ∧
    (∀ a b, gamma c a = gamma c b → c a b = 0 ∧ c b a = 0) := by
  refine ⟨h.diagonal 1, beta_one c, ?_, markerForm_invariant U c h,
    marker_period_three_on_beta U c h, (fun _ hx => marker_radical_stable U c h hx),
    markerQuotient_beta U c h, markerQuotient_three_beta U c h,
    (fun a => by simp [defect, beta_one]), (fun a => by simp [defect, beta_one]),
    anchoredSpan_quotient c (h.diagonal 1), beta_span c (h.diagonal 1),
    quotient_joint_nondegenerate c (h.diagonal 1), markerQuotient_three U c h,
    quotientForm_marker_invariant U c h, difference_diagonal U c h,
    q_average U c h, r_average U c h, quotient_bilinear_balance U c h,
    unweighted_sum U c h, inverse_weighted_sum U c h, marker_cyclotomic U c h,
    phase_children U c h, cross_defect_isotropic U c h, W_isotropic U c h,
    W_marker_image U c h, gamma_one c, gamma_mul c, gamma_marker U c h,
    gamma_phase_product U c h, gamma_fibre_zero_comparison U c h⟩
  exact quotientForm_beta c (h.diagonal 1)

/-- The actual zero fibre in the constructed quotient. -/
def N {M : Type*} [MulOneClass M] (c : M → M → ℝ) : Set M :=
  {a | gamma c a = 0}

/-- The actual ordered relation of equal gamma labels. -/
def K {M : Type*} [MulOneClass M] (c : M → M → ℝ) : Set (M × M) :=
  {p | gamma c p.1 = gamma c p.2}

private theorem comparison_bound {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b u v : M) :
    c (a * u) (b * v) ≤ 3 * (c a b + c u v) := by
  have hb := h.balance a b u v
  linarith [h.nonneg (a * U u) (b * U v), h.nonneg (a * U (U u)) (b * U (U v))]

private theorem directed_fibre_differences {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b z : M)
    (hab : (a, b) ∈ K c) :
    c a (b * z) - c b (b * z) =
        -2 * quotientForm c (beta c a - beta c b) (beta c z) ∧
      c (b * z) a - c (b * z) b =
        -2 * quotientForm c (beta c z) (beta c a - beta c b) := by
  have hw : beta c a - beta c b ∈ W c := (Submodule.Quotient.eq _).1 hab
  have hc := gamma_fibre_zero_comparison U c h a b hab
  have he : beta c (b * z) = beta c b + beta c z + defect c b z := by
    unfold defect
    abel
  constructor
  · have ht := W_isotropic U c h _ _ hw (defect_mem_W c b z)
    have hb : quotientForm c (beta c a - beta c b) (beta c (b * z)) =
        quotientForm c (beta c a - beta c b) (beta c b) +
        quotientForm c (beta c a - beta c b) (beta c z) := by
      rw [he, map_add, map_add, ht, add_zero]
    simp only [map_sub, LinearMap.sub_apply, quotientForm_beta c (h.diagonal 1),
      kernel, hc.1, h.diagonal] at hb
    simp only [map_sub, LinearMap.sub_apply, quotientForm_beta c (h.diagonal 1), kernel]
    linarith
  · have ht := W_isotropic U c h _ _ (defect_mem_W c b z) hw
    have hb : quotientForm c (beta c (b * z)) (beta c a - beta c b) =
        quotientForm c (beta c b) (beta c a - beta c b) +
        quotientForm c (beta c z) (beta c a - beta c b) := by
      rw [he, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, ht, add_zero]
    simp only [map_sub, quotientForm_beta c (h.diagonal 1), kernel, hc.2, h.diagonal] at hb
    simp only [map_sub, quotientForm_beta c (h.diagonal 1), kernel]
    linarith

private theorem directed_fibre_bounds {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b z : M)
    (hab : (a, b) ∈ K c) :
    |quotientForm c (beta c a - beta c b) (beta c z)| ≤ (3 / 2 : ℝ) * r c z ∧
      |quotientForm c (beta c z) (beta c a - beta c b)| ≤ (3 / 2 : ℝ) * q c z := by
  have hc := gamma_fibre_zero_comparison U c h a b hab
  have hd := directed_fibre_differences U c h a b z hab
  have h₁ := comparison_bound U c h a b 1 z
  have h₂ := comparison_bound U c h b b 1 z
  have h₃ := comparison_bound U c h b a z 1
  have h₄ := comparison_bound U c h b b z 1
  simp only [mul_one, hc.1, hc.2, h.diagonal, zero_add] at h₁ h₂ h₃ h₄
  dsimp [q, r]
  constructor <;> rw [abs_le] <;>
    constructor <;> linarith [hd.1, hd.2, h.nonneg a (b * z), h.nonneg b (b * z),
      h.nonneg (b * z) a, h.nonneg (b * z) b]

private theorem N_one {M : Type*} [MulOneClass M] (c : M → M → ℝ) : (1 : M) ∈ N c :=
  gamma_one c

private theorem N_marker {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) {a : M} (ha : a ∈ N c) :
    U a ∈ N c := by
  change gamma c (U a) = 0
  rw [gamma_marker U c h, ha, map_zero]

private theorem N_children {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) {u x : M}
    (hu : u ∈ N c) (hx : x ∈ N c) (k : ℕ) : x * U^[k] u ∈ N c := by
  change gamma c (x * U^[k] u) = 0
  rw [gamma_phase_product U c h, hx, hu, zero_add]
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply', ih, map_zero]

/-- The algebraic complex structure before any positivity claim. -/
def J {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) : V c →ₗ[ℝ] V c :=
  (Real.sqrt 3)⁻¹ • ((2 : ℝ) • markerQuotient U c h + LinearMap.id)

private theorem J_square {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : V c) :
    J U c h (J U c h x) = -x := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have he : J U c h (J U c h x) + x =
      (4 / 3 : ℝ) • (x + markerQuotient U c h x +
        markerQuotient U c h (markerQuotient U c h x)) := by
    simp only [J, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
      map_add, map_smul]
    match_scalars <;> field_simp <;> nlinarith
  rw [marker_cyclotomic U c h, smul_zero] at he
  exact eq_neg_iff_add_eq_zero.mpr he

private def phaseRoot : ℂ := ⟨-1 / 2, Real.sqrt 3 / 2⟩

private theorem phaseRoot_cube : phaseRoot ^ 3 = 1 := by
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hs₃ := congrArg (fun t : ℝ => t * Real.sqrt 3) hs
  apply Complex.ext <;> norm_num [phaseRoot, pow_succ, Complex.mul_re, Complex.mul_im]
  all_goals nlinarith

private def phaseCharacter : AddChar (ZMod 3) ℂ := AddChar.zmodChar 3 phaseRoot_cube

private theorem phase_cases (k : ZMod 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  have hk := k.val_lt
  have hc := (ZMod.natCast_zmod_val k).symm
  have hv : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 := by omega
  rcases hv with hv | hv | hv
  · left; simpa [hv] using hc
  · right; left; simpa [hv] using hc
  · right; right; simpa [hv] using hc

private theorem phaseCharacter_injective : Function.Injective phaseCharacter := by
  intro a b hab
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rcases phase_cases a with rfl | rfl | rfl
  all_goals rcases phase_cases b with rfl | rfl | rfl
  all_goals try rfl
  all_goals norm_num [phaseCharacter, AddChar.zmodChar_apply, ZMod.val_one, ZMod.val_ofNat,
      phaseRoot, pow_succ,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im] at hab
  all_goals nlinarith

private def complexMode {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (α : V c →ₗ[ℝ] ℝ) :
    V c →ₗ[ℝ] ℂ :=
  (Complex.ofRealLI.toLinearMap.comp α) -
    Complex.I • (Complex.ofRealLI.toLinearMap.comp (α.comp (J U c h)))

private theorem complexMode_re {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (α : V c →ₗ[ℝ] ℝ) (x : V c) :
    (complexMode U c h α x).re = α x := by
  simp [complexMode, Complex.mul_re]

private theorem complexMode_marker {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (α : V c →ₗ[ℝ] ℝ) (x : V c) :
    complexMode U c h α (markerQuotient U c h x) = phaseRoot * complexMode U c h α x := by
  have hn : Real.sqrt (3 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hj : complexMode U c h α (J U c h x) =
      Complex.I * complexMode U c h α x := by
    apply Complex.ext <;> simp [complexMode, J_square U c h, Complex.mul_re, Complex.mul_im]
  have hr : markerQuotient U c h x =
      (Real.sqrt 3 / 2) • J U c h x - (1 / 2 : ℝ) • x := by
    simp only [J, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply]
    match_scalars <;> field_simp <;> ring
  rw [hr, map_sub, map_smul, map_smul, hj]
  apply Complex.ext <;> simp [phaseRoot, Complex.mul_re, Complex.mul_im] <;> ring

private theorem complexMode_bound {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (α : V c →ₗ[ℝ] ℝ)
    (L : ℝ) (hL : 0 ≤ L) (ha : ∀ n ∈ N c, |α (beta c n)| ≤ L)
    (n : M) (hn : n ∈ N c) :
    Complex.normSq (complexMode U c h α (beta c n)) ≤ 10 * L ^ 2 := by
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs₁ : 1 ≤ Real.sqrt (3 : ℝ) := (Real.one_le_sqrt).2 (by norm_num)
  have h₀ := ha n hn
  have h₁ := ha (U n) (N_marker U c h hn)
  have hj : α (J U c h (beta c n)) =
      (Real.sqrt 3)⁻¹ * (2 * α (beta c (U n)) + α (beta c n)) := by
    simp [J, map_add, map_smul, markerQuotient_beta, smul_eq_mul]
    ring
  have hsum : |2 * α (beta c (U n)) + α (beta c n)| ≤ 3 * L := by
    rw [abs_le] at h₀ h₁ ⊢
    constructor <;> linarith [h₀.1, h₀.2, h₁.1, h₁.2]
  have hjabs : |α (J U c h (beta c n))| ≤ 3 * L := by
    rw [hj, abs_mul, abs_inv, abs_of_pos hs]
    calc
      _ = |2 * α (beta c (U n)) + α (beta c n)| / Real.sqrt 3 := by ring
      _ ≤ (3 * L) / Real.sqrt 3 := div_le_div_of_nonneg_right hsum (le_of_lt hs)
      _ ≤ 3 * L := by
        apply (div_le_iff₀ hs).2
        nlinarith [mul_nonneg hL (sub_nonneg.mpr hs₁)]
  have hsq₀ : α (beta c n) ^ 2 ≤ L ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hL).2 h₀
  have hsq₁ : α (J U c h (beta c n)) ^ 2 ≤ (3 * L) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 3 * L)).2 hjabs
  simp [Complex.normSq_apply, complexMode, Complex.mul_re, Complex.mul_im]
  nlinarith

private theorem actual_mode_recursion {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (α : V c →ₗ[ℝ] ℝ)
    (a u : M) (k : ZMod 3) :
    complexMode U c h α (beta c (a * U^[k.val] u)) =
      complexMode U c h α (beta c a) +
      phaseCharacter k * complexMode U c h α (beta c u) +
      phaseCharacter⁻¹ k * complexMode U c h α (defect c a u) := by
  have hp := (raw_anchored_radical_descent U c h).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a u
  have h₀ : beta c (a * u) = beta c a + beta c u + defect c a u := by
    unfold defect
    abel
  rcases phase_cases k with rfl | rfl | rfl
  all_goals norm_num [phaseCharacter, AddChar.zmodChar_apply, AddChar.inv_apply,
    ZMod.val_one, ZMod.val_ofNat, show -(2 : ZMod 3) = 1 by decide,
    Function.iterate_succ_apply']
  · rw [h₀, map_add, map_add]
  · rw [hp.1, map_add, map_add]
    simp only [complexMode_marker]
    ring
  · rw [hp.2, map_add, map_add]
    simp only [complexMode_marker, show (-2 : ZMod 3).val = 1 by decide, pow_one]
    ring

/-- Every actual zero-fibre label has zero beta, using both directed history bounds. -/
theorem raw_zero_fibre_vanishes {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    ∀ u ∈ N c, beta c u = 0 := by
  intro u hu
  apply quotient_joint_nondegenerate c (h.diagonal 1)
  · intro z
    let α : V c →ₗ[ℝ] ℝ := (quotientForm c).flip (beta c z)
    let L : ℝ := (3 / 2 : ℝ) * r c z
    have hL : 0 ≤ L := mul_nonneg (by norm_num) (h.nonneg 1 z)
    have ha (n : M) (hn : n ∈ N c) : |α (beta c n)| ≤ L := by
      have hk : (n, 1) ∈ K c := by change gamma c n = gamma c 1; rw [hn, gamma_one]
      simpa [α, beta_one] using (directed_fibre_bounds U c h n 1 z hk).1
    have hv := D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity.bounded_phase_recursion_vanishes
      U u (N c) (N_one c) (fun x hx k => N_children U c h hu hx k.val)
      phaseCharacter phaseCharacter_injective
      (fun x => complexMode U c h α (beta c x))
      (fun x => complexMode U c h α (defect c x u)) (10 * L ^ 2)
      (fun x hx => complexMode_bound U c h α L hL ha x hx)
      (fun x _ k => actual_mode_recursion U c h α x u k)
    have hre := congrArg Complex.re hv
    simpa [complexMode_re, α] using hre
  · intro z
    let α : V c →ₗ[ℝ] ℝ := quotientForm c (beta c z)
    let L : ℝ := (3 / 2 : ℝ) * q c z
    have hL : 0 ≤ L := mul_nonneg (by norm_num) (h.nonneg z 1)
    have ha (n : M) (hn : n ∈ N c) : |α (beta c n)| ≤ L := by
      have hk : (n, 1) ∈ K c := by change gamma c n = gamma c 1; rw [hn, gamma_one]
      simpa [α, beta_one] using (directed_fibre_bounds U c h n 1 z hk).2
    have hv := D5.S3.Quantum.Completion.ThreePhaseHistoryRigidity.bounded_phase_recursion_vanishes
      U u (N c) (N_one c) (fun x hx k => N_children U c h hu hx k.val)
      phaseCharacter phaseCharacter_injective
      (fun x => complexMode U c h α (beta c x))
      (fun x => complexMode U c h α (defect c x u)) (10 * L ^ 2)
      (fun x hx => complexMode_bound U c h α L hL ha x hx)
      (fun x _ k => actual_mode_recursion U c h α x u k)
    have hre := congrArg Complex.re hv
    simpa [complexMode_re, α] using hre

private theorem gamma_inverse_label {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) :
    gamma c (U a * U (U a)) = -gamma c a := by
  have hc := congrArg (W c).mkQ (marker_cyclotomic U c h (beta c a))
  simp only [map_add, map_zero, markerQuotient_beta] at hc
  change gamma c a + gamma c (U a) + gamma c (U (U a)) = 0 at hc
  rw [gamma_mul]
  apply eq_neg_iff_add_eq_zero.mpr
  convert hc using 1 <;> abel

private theorem fibre_linear_vanishes {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (α : V c →ₗ[ℝ] ℝ) (L : ℝ)
    (hb : ∀ a b, (a, b) ∈ K c → |α (beta c a - beta c b)| ≤ L) :
    ∀ a b, (a, b) ∈ K c → α (beta c a - beta c b) = 0 := by
  let S : Set ℝ := Set.range (fun p : {p : M × M // p ∈ K c} =>
    |α (beta c p.val.1 - beta c p.val.2)|)
  have hne : S.Nonempty := ⟨0, ⟨⟨(1, 1), rfl⟩, by simp⟩⟩
  have hbd : BddAbove S := by
    refine ⟨L, ?_⟩
    rintro t ⟨p, rfl⟩
    exact hb _ _ p.property
  have hup (a b : M) (hab : (a, b) ∈ K c) :
      |α (beta c a - beta c b)| ≤ sSup S :=
    le_csSup hbd ⟨⟨(a, b), hab⟩, rfl⟩
  have hcontract (a b : M) (hab : (a, b) ∈ K c) :
      |α (beta c a - beta c b)| ≤ (2 / 3 : ℝ) * sSup S := by
    let d := U a * U (U a)
    have haN : a * d ∈ N c := by
      change gamma c (a * d) = 0
      rw [gamma_mul, gamma_inverse_label U c h]
      exact add_neg_cancel _
    have hbN : b * d ∈ N c := by
      change gamma c (b * d) = 0
      rw [gamma_mul, gamma_inverse_label U c h]
      change gamma c a = gamma c b at hab
      rw [hab, add_neg_cancel]
    have hz : α (beta c (a * d) - beta c (b * d)) = 0 := by
      rw [raw_zero_fibre_vanishes U c h _ haN, raw_zero_fibre_vanishes U c h _ hbN]
      simp
    have hk (t : M) : (a * t, b * t) ∈ K c := by
      change gamma c (a * t) = gamma c (b * t)
      rw [gamma_mul, gamma_mul, show gamma c a = gamma c b from hab]
    have he₁ := congrArg α (unweighted_sum U c h a d)
    have he₂ := congrArg α (unweighted_sum U c h b d)
    simp only [map_add, map_smul, smul_eq_mul] at he₁ he₂
    have he : 3 * α (beta c a - beta c b) =
        α (beta c (a * U d) - beta c (b * U d)) +
        α (beta c (a * U (U d)) - beta c (b * U (U d))) := by
      simp only [map_sub] at hz ⊢
      linarith
    have ht : |3 * α (beta c a - beta c b)| ≤ sSup S + sSup S := by
      rw [he]
      exact (abs_add_le _ _).trans
        (add_le_add (hup _ _ (hk (U d))) (hup _ _ (hk (U (U d)))))
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at ht
    linarith
  have hs : sSup S ≤ (2 / 3 : ℝ) * sSup S := by
    apply csSup_le hne
    rintro t ⟨p, rfl⟩
    exact hcontract _ _ p.property
  have hs0 : sSup S ≤ 0 := by linarith
  intro a b hab
  exact abs_eq_zero.mp (le_antisymm ((hup a b hab).trans hs0) (abs_nonneg _))

/-- The same original gamma fibre has a unique anchored comparison vector. -/
theorem raw_gamma_fibre_collapse {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M)
    (hab : gamma c a = gamma c b) : beta c a = beta c b := by
  apply sub_eq_zero.mp
  apply quotient_joint_nondegenerate c (h.diagonal 1)
  · intro z
    exact fibre_linear_vanishes U c h ((quotientForm c).flip (beta c z))
      ((3 / 2 : ℝ) * r c z) (fun x y hxy => (directed_fibre_bounds U c h x y z hxy).1)
      a b hab
  · intro z
    exact fibre_linear_vanishes U c h (quotientForm c (beta c z))
      ((3 / 2 : ℝ) * q c z) (fun x y hxy => (directed_fibre_bounds U c h x y z hxy).2)
      a b hab

/-- Both one-point and both ordered comparison readouts are constant on actual gamma fibres. -/
theorem raw_directed_comparison_descent {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M)
    (hab : gamma c a = gamma c b) :
    q c a = q c b ∧ r c a = r c b ∧
      (∀ z, c a z = c b z) ∧ (∀ z, c z a = c z b) := by
  have hv := raw_gamma_fibre_collapse U c h a b hab
  have hc := gamma_fibre_zero_comparison U c h a b hab
  have h₁ := congrArg (fun x => quotientForm c x (beta c b)) hv
  have h₂ := congrArg (quotientForm c (beta c a)) hv
  simp only [quotientForm_beta c (h.diagonal 1), kernel, h.diagonal, hc.1] at h₁ h₂
  have hq : q c a = q c b := by linarith
  have hr : r c a = r c b := by linarith
  refine ⟨hq, hr, ?_, ?_⟩
  · intro z
    have hz := congrArg (fun x => quotientForm c x (beta c z)) hv
    simp only [quotientForm_beta c (h.diagonal 1), kernel] at hz
    linarith
  · intro z
    have hz := congrArg (quotientForm c (beta c z)) hv
    simp only [quotientForm_beta c (h.diagonal 1), kernel] at hz
    linarith

/-- The actual gamma image, closed under addition and the original inverse label. -/
def visibleGroup {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) : AddSubgroup (GammaSpace c) where
  carrier := Set.range (gamma c)
  zero_mem' := ⟨1, gamma_one c⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a * b, gamma_mul c a b⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨U a * U (U a), gamma_inverse_label U c h a⟩

def visibleLabel {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) : visibleGroup U c h :=
  ⟨gamma c a, ⟨a, rfl⟩⟩

private theorem visibleLabel_surjective {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    Function.Surjective (visibleLabel U c h) := by
  rintro ⟨x, a, rfl⟩
  exact ⟨a, rfl⟩

private theorem visibleLabel_mul {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M) :
    visibleLabel U c h (a * b) = visibleLabel U c h a + visibleLabel U c h b :=
  Subtype.ext (gamma_mul c a b)

def visibleMarker {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) :
    visibleGroup U c h →+ visibleGroup U c h where
  toFun x := ⟨rho U c h x.val, by
    obtain ⟨a, ha⟩ := x.property
    exact ⟨U a, (gamma_marker U c h a).trans (congrArg (rho U c h) ha)⟩⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

private theorem visibleLabel_marker {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a : M) :
    visibleLabel U c h (U a) = visibleMarker U c h (visibleLabel U c h a) :=
  Subtype.ext (gamma_marker U c h a)

private def originalLabel {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : visibleGroup U c h) : M :=
  Classical.choose x.property

private theorem originalLabel_spec {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : visibleGroup U c h) :
    gamma c (originalLabel U c h x) = x.val := Classical.choose_spec x.property

/-- The full directed comparison on the actual additive image. -/
def visibleComparison {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (x y : visibleGroup U c h) : ℝ := c (originalLabel U c h x) (originalLabel U c h y)

private theorem visibleComparison_label {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (a b : M) :
    visibleComparison U c h (visibleLabel U c h a) (visibleLabel U c h b) = c a b := by
  have ha := raw_directed_comparison_descent U c h _ a
    (originalLabel_spec U c h (visibleLabel U c h a))
  have hb := raw_directed_comparison_descent U c h _ b
    (originalLabel_spec U c h (visibleLabel U c h b))
  exact (ha.2.2.1 _).trans (hb.2.2.2 _)

private theorem visibleComparison_nonneg {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x y : visibleGroup U c h) :
    0 ≤ visibleComparison U c h x y := h.nonneg _ _

private theorem visibleComparison_diagonal {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x : visibleGroup U c h) :
    visibleComparison U c h x x = 0 := h.diagonal _

private theorem visibleComparison_balance {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c) (x y u v : visibleGroup U c h) :
    visibleComparison U c h (x + u) (y + v) +
      visibleComparison U c h (x + visibleMarker U c h u) (y + visibleMarker U c h v) +
      visibleComparison U c h (x + visibleMarker U c h (visibleMarker U c h u))
        (y + visibleMarker U c h (visibleMarker U c h v)) =
      3 * visibleComparison U c h x y + 3 * visibleComparison U c h u v := by
  obtain ⟨a, rfl⟩ := visibleLabel_surjective U c h x
  obtain ⟨b, rfl⟩ := visibleLabel_surjective U c h y
  obtain ⟨d, rfl⟩ := visibleLabel_surjective U c h u
  obtain ⟨e, rfl⟩ := visibleLabel_surjective U c h v
  have hb :
      visibleComparison U c h (visibleLabel U c h (a * d)) (visibleLabel U c h (b * e)) +
      visibleComparison U c h (visibleLabel U c h (a * U d)) (visibleLabel U c h (b * U e)) +
      visibleComparison U c h (visibleLabel U c h (a * U (U d)))
        (visibleLabel U c h (b * U (U e))) =
      3 * visibleComparison U c h (visibleLabel U c h a) (visibleLabel U c h b) +
      3 * visibleComparison U c h (visibleLabel U c h d) (visibleLabel U c h e) := by
    simpa only [visibleComparison_label] using h.balance a b d e
  simpa only [visibleLabel_mul, visibleLabel_marker] using hb

/-- The original directed comparison on the constructed image is translation invariant. -/
theorem raw_visible_translation_invariant {M : Type*} [MulOneClass M]
    (U : M → M) (c : M → M → ℝ) (h : RawBalance U c)
    (x y z : visibleGroup U c h) :
    visibleComparison U c h (x + z) (y + z) = visibleComparison U c h x y := by
  let f : visibleGroup U c h → ℝ := fun t => visibleComparison U c h (x + t) (y + t)
  let S : Set ℝ := Set.range f
  have hne : S.Nonempty := ⟨f 0, ⟨0, rfl⟩⟩
  have hbd : BddBelow S := by
    refine ⟨0, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact visibleComparison_nonneg U c h _ _
  have hm (t : visibleGroup U c h) : sInf S ≤ f t := csInf_le hbd ⟨t, rfl⟩
  have hstep (t w : visibleGroup U c h) : f (t + w) ≤ 3 * f t - 2 * sInf S := by
    have hb := visibleComparison_balance U c h (x + t) (y + t) w w
    rw [visibleComparison_diagonal] at hb
    simp only [add_assoc] at hb
    change f (t + w) + f (t + visibleMarker U c h w) +
      f (t + visibleMarker U c h (visibleMarker U c h w)) = 3 * f t + 3 * 0 at hb
    linarith [hm (t + visibleMarker U c h w),
      hm (t + visibleMarker U c h (visibleMarker U c h w))]
  have heq (s : visibleGroup U c h) : f s = sInf S := by
    have hlow : (f s + 2 * sInf S) / 3 ≤ sInf S := by
      apply le_csInf hne
      rintro _ ⟨t, rfl⟩
      have ht := hstep t (s - t)
      have he : t + (s - t) = s := by abel
      rw [he] at ht
      linarith
    exact le_antisymm (by linarith) (hm s)
  have hz := (heq z).trans (heq 0).symm
  simpa only [f, add_zero] using hz

end D5.S3.Quantum.Completion.RawAnchoredRadicalDescent
