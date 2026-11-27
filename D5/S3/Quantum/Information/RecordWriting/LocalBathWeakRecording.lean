/- GID: D5/S3/Quantum/Information/RecordWriting/LocalBathWeakRecording
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/RecordWriting/LocalBathWeakRecording
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Bounds weak recording with local baths and collective reversible control. -/

import D5.S3.Quantum.Information.RecordWriting.TwoRegister
import D5.S3.TotalVariation.Pinsker
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp

/-! Omega original.

Finite scheduled local baths on a binary cube. The transition probabilities are
shared across the spectator fibers of the selected bit. The dissipation assumption
is edgewise, at the actual forward and backward fluxes of the bath step.
Source for the collective-gate question: Chung, arXiv:2611.34909v1, §VIII,
final paragraph. Coordinate-sign orthogonality turns the local flux bound
into a product bound for multiple readable records. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace D5.S3.Quantum.Information.RecordWriting.LocalBathWeakRecording

open TwoRegister (Law sign)

variable {ι : Type} [Fintype ι] [DecidableEq ι]

abbrev Point (ι : Type) := ι → Bool
abbrev Fiber {ι : Type} (i : ι) := {j : ι // j ≠ i} → Bool

private def split (i : ι) : Point ι ≃ Bool × Fiber i :=
  Equiv.piSplitAt i (fun _ => Bool)

def endpoint (i : ι) (b : Bool) (y : Fiber i) : Point ι :=
  (split i).symm (b, y)

private theorem sum_fibers (i : ι) (f : Point ι → ℝ) :
    (∑ x, f x) = ∑ y : Fiber i, (f (endpoint i false y) + f (endpoint i true y)) := by
  rw [← (split i).symm.sum_comp f, Fintype.sum_prod_type, Fintype.sum_bool,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  simp [endpoint, add_comm]

/-- The number of joint states, including the singleton cube with no bits. -/
def dimension (ι : Type) [Fintype ι] [DecidableEq ι] : ℝ := Fintype.card (Point ι)

private theorem dimension_pos (ι : Type) [Fintype ι] [DecidableEq ι] : 0 < dimension ι := by
  unfold dimension
  exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (Point ι))

private theorem dimension_split (i : ι) :
    dimension ι = 2 * (Fintype.card (Fiber i) : ℝ) := by
  have h : Fintype.card (Point ι) = 2 * Fintype.card (Fiber i) := by
    simpa using Fintype.card_congr (split i)
  unfold dimension
  exact_mod_cast h

def uniform : Law (Point ι) where
  mass _ := (dimension ι)⁻¹
  nonneg _ := inv_nonneg.mpr (dimension_pos ι).le
  normalized := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact mul_inv_cancel₀ (dimension_pos ι).ne'

def permute (e : Equiv.Perm (Point ι)) (p : Law (Point ι)) : Law (Point ι) where
  mass x := p.mass (e.symm x)
  nonneg _ := p.nonneg _
  normalized := (Equiv.sum_comp e.symm p.mass).trans p.normalized

/-- An up and a down probability for a single scheduled bath step. Every
spectator assignment uses the same two numbers. -/
structure Rates where
  up : ℝ
  down : ℝ
  up_nonneg : 0 ≤ up
  down_nonneg : 0 ≤ down
  up_le_one : up ≤ 1
  down_le_one : down ≤ 1

/-- The instantaneous oriented current for a shared pair of nonnegative rates.
The same formula gives the mass moved in a step when the rates are step weights. -/
def current (i : ι) (up down : ℝ) (p : Law (Point ι)) (y : Fiber i) : ℝ :=
  up * p.mass (endpoint i false y) - down * p.mass (endpoint i true y)

/-- The sum of the forward and backward flux on one undirected edge. -/
def edgeActivity (i : ι) (up down : ℝ) (p : Law (Point ι)) (y : Fiber i) : ℝ :=
  up * p.mass (endpoint i false y) + down * p.mass (endpoint i true y)

/-- The local entropy-production premise, in multiplied form. This permits an
inactive edge with zero current without requiring division by its activity. -/
def FluxBound (i : ι) (up down : ℝ) (p : Law (Point ι)) (σ : Fiber i → ℝ) : Prop :=
  ∀ y, 0 ≤ σ y ∧ 2 * current i up down p y ^ 2 ≤ edgeActivity i up down p y * σ y

private theorem activity_nonneg (i : ι) {up down : ℝ} (hu : 0 ≤ up) (hd : 0 ≤ down)
    (p : Law (Point ι)) (y : Fiber i) : 0 ≤ edgeActivity i up down p y :=
  add_nonneg (mul_nonneg hu (p.nonneg _)) (mul_nonneg hd (p.nonneg _))

private theorem positive_flux_log_bound {f g : ℝ} (hf : 0 < f) (hg : 0 < g) :
    0 ≤ (f - g) * Real.log (f / g) ∧
      2 * (f - g) ^ 2 ≤ (f + g) * ((f - g) * Real.log (f / g)) := by
  let a := f + g
  have ha : 0 < a := add_pos hf hg
  let u := f / a
  let v := g / a
  have hu : 0 < u := div_pos hf ha
  have hv : 0 < v := div_pos hg ha
  have huv : u + v = 1 := by
    change f / a + g / a = 1
    rw [← add_div]
    exact div_self ha.ne'
  have huc : 1 - u = v := by linarith
  have hvc : 1 - v = u := by linarith
  have hfor : u / v = f / g := by
    dsimp only [u, v]
    field_simp [ha.ne', hg.ne'] <;> ring
  have hrev : v / u = g / f := by
    dsimp only [u, v]
    field_simp [ha.ne', hf.ne'] <;> ring
  have hp := D5.S3.TotalVariation.Pinsker.binary_pinsker u v
    ⟨hu.le, by linarith⟩ ⟨hv.le, by linarith⟩
    (fun h => (hv.ne' h).elim) (fun h => (hu.ne' (hvc.symm.trans h)).elim)
  rw [huc, hvc, hfor, hrev] at hp
  have H := mul_le_mul_of_nonneg_left hp (sq_nonneg a)
  have hl : a ^ 2 * (2 * (u - v) ^ 2) = 2 * (f - g) ^ 2 := by
    dsimp only [u, v]
    field_simp [ha.ne'] <;> ring
  have hr : a ^ 2 * (u * Real.log (f / g) + v * Real.log (g / f)) =
      a * ((f - g) * Real.log (f / g)) := by
    rw [Real.log_div hf.ne' hg.ne', Real.log_div hg.ne' hf.ne']
    dsimp only [u, v]
    field_simp [ha.ne'] <;> ring
  rw [hl, hr] at H
  have hnon : 0 ≤ a * ((f - g) * Real.log (f / g)) :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg (f - g))).trans H
  exact ⟨nonneg_of_mul_nonneg_right hnon ha, H⟩

/-- The flux-affinity charge of a two-way edge. Each directional flux is
measured at the input law of the discrete step. -/
def logCharge (i : ι) (up down : ℝ) (p : Law (Point ι)) (y : Fiber i) : ℝ :=
  current i up down p y *
    Real.log ((up * p.mass (endpoint i false y)) / (down * p.mass (endpoint i true y)))

/-- Binary Pinsker gives the flux certificate when an edge has two positive
fluxes or two zero fluxes. A one-way positive flux needs a separate cost
model allowing infinite charge. -/
theorem logCharge_fluxBound (i : ι) {up down : ℝ} (hu : 0 ≤ up) (hd : 0 ≤ down)
    (p : Law (Point ι))
    (hsupport : ∀ y : Fiber i,
      up * p.mass (endpoint i false y) = 0 ↔ down * p.mass (endpoint i true y) = 0) :
    FluxBound i up down p (logCharge i up down p) := by
  intro y
  by_cases hf : up * p.mass (endpoint i false y) = 0
  · have hg := (hsupport y).mp hf
    simp [logCharge, current, edgeActivity, hf, hg]
  · have hg : down * p.mass (endpoint i true y) ≠ 0 := fun h => hf ((hsupport y).mpr h)
    exact positive_flux_log_bound
      (lt_of_le_of_ne (mul_nonneg hu (p.nonneg _)) (Ne.symm hf))
      (lt_of_le_of_ne (mul_nonneg hd (p.nonneg _)) (Ne.symm hg))

/-- The divergence of the local current on the disjoint pairs of the selected bit. -/
def generator (i : ι) (up down : ℝ) (p : Law (Point ι)) (x : Point ι) : ℝ :=
  if (split i x).1 then
    current i up down p (split i x).2
  else
    -current i up down p (split i x).2

private theorem generator_endpoint (i : ι) (up down : ℝ) (p : Law (Point ι))
    (b : Bool) (y : Fiber i) :
    generator i up down p (endpoint i b y) =
      if b then current i up down p y else -current i up down p y := by
  simp only [generator, endpoint, Equiv.apply_symm_apply]

/-- Apply the two-by-two stochastic matrix independently on each fiber. -/
def Rates.apply (r : Rates) (i : ι) (p : Law (Point ι)) : Law (Point ι) where
  mass x := p.mass x + generator i r.up r.down p x
  nonneg x := by
    let z := split i x
    have hx : endpoint i z.1 z.2 = x := (split i).symm_apply_apply x
    rw [← hx, generator_endpoint]
    cases hz : z.1 with
    | false =>
        simp only [hz, Bool.false_eq_true, if_false, current]
        have h := add_nonneg
          (mul_nonneg (sub_nonneg.mpr r.up_le_one) (p.nonneg (endpoint i false z.2)))
          (mul_nonneg r.down_nonneg (p.nonneg (endpoint i true z.2)))
        linarith
    | true =>
        simp only [hz, if_true, current]
        have h := add_nonneg
          (mul_nonneg (sub_nonneg.mpr r.down_le_one) (p.nonneg (endpoint i true z.2)))
          (mul_nonneg r.up_nonneg (p.nonneg (endpoint i false z.2)))
        linarith
  normalized := by
    rw [Finset.sum_add_distrib, p.normalized, sum_fibers i (generator i r.up r.down p)]
    simp [generator_endpoint]

/-- Exact finite-step identity relating the stochastic update to its generator. -/
theorem Rates.apply_sub (r : Rates) (i : ι) (p : Law (Point ι)) (x : Point ι) :
    (r.apply i p).mass x - p.mass x = generator i r.up r.down p x := by
  change p.mass x + generator i r.up r.down p x - p.mass x = _
  ring

def massVector (f : Point ι → ℝ) : EuclideanSpace ℝ (Point ι) :=
  WithLp.toLp 2 (fun x => Real.sqrt (dimension ι) * f x)

private theorem massVector_norm_sq (f : Point ι → ℝ) :
    ‖massVector f‖ ^ 2 = dimension ι * ∑ x, f x ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  change (Real.sqrt (dimension ι) * f x) ^ 2 = dimension ι * f x ^ 2
  rw [mul_pow, Real.sq_sqrt (dimension_pos ι).le]

private theorem generator_norm_sq (i : ι) (up down : ℝ) (p : Law (Point ι)) :
    ‖massVector (generator i up down p)‖ ^ 2 =
      2 * dimension ι * ∑ y, current i up down p y ^ 2 := by
  rw [massVector_norm_sq, sum_fibers i (fun x => generator i up down p x ^ 2)]
  simp only [generator_endpoint, Bool.false_eq_true, if_false, if_true, neg_sq]
  simp_rw [← two_mul]
  rw [← Finset.mul_sum]
  ring

/-- Shared rates and disjoint fibers give the bath-generator estimate. The
uniform tube uses masses scaled by the number of joint states. -/
theorem generator_bound (i : ι) {up down q : ℝ} (hu : 0 ≤ up) (hd : 0 ≤ down)
    (hq₀ : 0 ≤ q) (hq₁ : q < 1) (p : Law (Point ι)) (σ : Fiber i → ℝ)
    (hσ : FluxBound i up down p σ)
    (htube : ∀ x, 1 - q ≤ dimension ι * p.mass x ∧ dimension ι * p.mass x ≤ 1 + q) :
    ‖massVector (generator i up down p)‖ ^ 2 ≤
      2 * ((1 + q) / (1 - q)) * (∑ y, edgeActivity i up down p y) * ∑ y, σ y := by
  let d := dimension ι
  let a := edgeActivity i up down p
  let A := ∑ y, a y
  have hlo (y : Fiber i) : (up + down) * (1 - q) ≤ d * a y := by
    calc
      _ = up * (1 - q) + down * (1 - q) := by ring
      _ ≤ up * (d * p.mass (endpoint i false y)) + down * (d * p.mass (endpoint i true y)) :=
        add_le_add (mul_le_mul_of_nonneg_left (htube _).1 hu)
          (mul_le_mul_of_nonneg_left (htube _).1 hd)
      _ = d * a y := by dsimp [a, edgeActivity]; ring
  have hhi (y : Fiber i) : d * a y ≤ (up + down) * (1 + q) := by
    calc
      _ = up * (d * p.mass (endpoint i false y)) + down * (d * p.mass (endpoint i true y)) := by
        dsimp [a, edgeActivity]; ring
      _ ≤ up * (1 + q) + down * (1 + q) :=
        add_le_add (mul_le_mul_of_nonneg_left (htube _).2 hu)
          (mul_le_mul_of_nonneg_left (htube _).2 hd)
      _ = _ := by ring
  have hlower : (up + down) * (1 - q) ≤ 2 * A := by
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hlo y)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.mul_sum] at hsum
    have hcard : d = 2 * (Fintype.card (Fiber i) : ℝ) := dimension_split i
    have hdp : 0 < d := dimension_pos ι
    apply le_of_mul_le_mul_left _ hdp
    calc
      d * ((up + down) * (1 - q)) =
          2 * ((Fintype.card (Fiber i) : ℝ) * ((up + down) * (1 - q))) := by rw [hcard]; ring
      _ ≤ 2 * (d * A) := mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = d * (2 * A) := by ring
  have hpos : 0 < 1 - q := sub_pos.mpr hq₁
  have huniform (y : Fiber i) : d * a y ≤ 2 * ((1 + q) / (1 - q)) * A := by
    have h : d * a y * (1 - q) ≤ (1 + q) * (2 * A) := by
      calc
        _ ≤ ((up + down) * (1 + q)) * (1 - q) :=
          mul_le_mul_of_nonneg_right (hhi y) hpos.le
        _ = (1 + q) * ((up + down) * (1 - q)) := by ring
        _ ≤ (1 + q) * (2 * A) := mul_le_mul_of_nonneg_left hlower (by linarith)
    calc
      _ ≤ ((1 + q) * (2 * A)) / (1 - q) := (le_div_iff₀ hpos).mpr h
      _ = _ := by ring
  rw [generator_norm_sq]
  change 2 * d * (∑ y, current i up down p y ^ 2) ≤
    2 * ((1 + q) / (1 - q)) * A * ∑ y, σ y
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y _
  calc
    2 * d * current i up down p y ^ 2 = d * (2 * current i up down p y ^ 2) := by ring
    _ ≤ d * (a y * σ y) := mul_le_mul_of_nonneg_left (hσ y).2 (dimension_pos ι).le
    _ = (d * a y) * σ y := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (huniform y) (hσ y).1

/-- The generator bound controls the actual Euclidean displacement in one
driven step, for any local flux certificate at the input law. -/
theorem Rates.step_bound (r : Rates) (i : ι) {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (p : Law (Point ι)) (σ : Fiber i → ℝ) (hσ : FluxBound i r.up r.down p σ)
    (htube : ∀ x, 1 - q ≤ dimension ι * p.mass x ∧ dimension ι * p.mass x ≤ 1 + q) :
    ‖massVector (fun x => (r.apply i p).mass x - p.mass x)‖ ^ 2 ≤
      2 * ((1 + q) / (1 - q)) * (∑ y, edgeActivity i r.up r.down p y) * ∑ y, σ y := by
  simp_rw [Rates.apply_sub]
  exact generator_bound i r.up_nonneg r.down_nonneg hq₀ hq₁ p σ hσ htube


/-- The finite sequence is indexed by its input law. A bath carries its
edgewise charge certificate at the deterministic input law of that step.
Each branch can choose a different sequence of baths and joint permutations. -/
inductive Protocol : Law (Point ι) → Type
  | stop {p : Law (Point ι)} : Protocol p
  | gate {p : Law (Point ι)} (e : Equiv.Perm (Point ι))
      (rest : Protocol (permute e p)) : Protocol p
  | bath (p : Law (Point ι)) (i : ι) (r : Rates) (σ : Fiber i → ℝ)
      (certificate : FluxBound i r.up r.down p σ)
      (rest : Protocol (r.apply i p)) : Protocol p

def Protocol.final {p : Law (Point ι)} : Protocol p → Law (Point ι)
  | .stop => p
  | .gate _ rest => rest.final
  | .bath _ _ _ _ _ rest => rest.final

def Protocol.activity {p : Law (Point ι)} : Protocol p → ℝ
  | .stop => 0
  | .gate _ rest => rest.activity
  | .bath p i r _ _ rest => (∑ y, edgeActivity i r.up r.down p y) + rest.activity

def Protocol.entropy {p : Law (Point ι)} : Protocol p → ℝ
  | .stop => 0
  | .gate _ rest => rest.entropy
  | .bath _ _ _ σ _ rest => (∑ y, σ y) + rest.entropy

private def bathLength (i : ι) (r : Rates) (p : Law (Point ι)) : ℝ :=
  ∑ y, |current i r.up r.down p y|

def Protocol.length {p : Law (Point ι)} : Protocol p → ℝ
  | .stop => 0
  | .gate _ rest => rest.length
  | .bath p i r _ _ rest => bathLength i r p + rest.length

private theorem bathLength_nonneg (i : ι) (r : Rates) (p : Law (Point ι)) :
    0 ≤ bathLength i r p := Finset.sum_nonneg fun _ _ => abs_nonneg _

private theorem Protocol.cost_nonneg {p : Law (Point ι)} (t : Protocol p) :
    0 ≤ t.activity ∧ 0 ≤ t.entropy ∧ 0 ≤ t.length := by
  induction t with
  | stop => simp [Protocol.activity, Protocol.entropy, Protocol.length]
  | gate _ _ ih => exact ih
  | bath p i r σ hσ rest ih =>
      exact ⟨add_nonneg (Finset.sum_nonneg fun y _ =>
          activity_nonneg i r.up_nonneg r.down_nonneg p y) ih.1,
        add_nonneg (Finset.sum_nonneg fun y _ => (hσ y).1) ih.2.1,
        add_nonneg (bathLength_nonneg i r p) ih.2.2⟩

private theorem add_sq_bound {x y a b s t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hx : x ^ 2 ≤ a * s) (hy : y ^ 2 ≤ b * t) :
    (x + y) ^ 2 ≤ (a + b) * (s + t) := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.univ : Finset Bool)
    (r := fun z => if z then y else x)
    (f := fun z => if z then b else a)
    (g := fun z => if z then t else s)
    (fun z _ => by cases z <;> first | exact ha | exact hb)
    (fun z _ => by cases z <;> first | exact hs | exact ht)
    (fun z _ => by cases z <;> first | exact hx | exact hy)
  simpa [Fintype.sum_bool, add_comm] using h

private theorem bathLength_sq (i : ι) (r : Rates) (p : Law (Point ι))
    (σ : Fiber i → ℝ) (hσ : FluxBound i r.up r.down p σ) :
    bathLength i r p ^ 2 ≤ ((∑ y, edgeActivity i r.up r.down p y) / 2) * ∑ y, σ y := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun y => |current i r.up r.down p y|)
    (f := fun y => (1 / 2 : ℝ) * edgeActivity i r.up r.down p y)
    (g := σ)
    (fun y _ => mul_nonneg (by norm_num) (activity_nonneg i r.up_nonneg r.down_nonneg p y))
    (fun y _ => (hσ y).1)
    (fun y _ => by rw [sq_abs]; linarith [(hσ y).2])
  rw [← Finset.mul_sum] at h
  unfold bathLength
  convert h using 1 <;> ring

private theorem Protocol.length_sq {p : Law (Point ι)} (t : Protocol p) :
    t.length ^ 2 ≤ (t.activity / 2) * t.entropy := by
  induction t with
  | stop => norm_num [Protocol.length, Protocol.activity, Protocol.entropy]
  | gate _ _ ih => exact ih
  | bath p i r σ hσ rest ih =>
      have hA : 0 ≤ ∑ y, edgeActivity i r.up r.down p y :=
        Finset.sum_nonneg fun y _ => activity_nonneg i r.up_nonneg r.down_nonneg p y
      have hS : 0 ≤ ∑ y, σ y := Finset.sum_nonneg fun y _ => (hσ y).1
      simp only [Protocol.length, Protocol.activity, Protocol.entropy, add_div]
      exact add_sq_bound (div_nonneg hA (by norm_num))
        (div_nonneg rest.cost_nonneg.1 (by norm_num)) hS rest.cost_nonneg.2.1
        (bathLength_sq i r p σ hσ) ih

private theorem bath_coordinate_displacement (i : ι) (r : Rates) (p : Law (Point ι))
    (x : Point ι) : |(r.apply i p).mass x - p.mass x| ≤ bathLength i r p := by
  rw [r.apply_sub]
  have heq : |generator i r.up r.down p x| =
      |current i r.up r.down p (split i x).2| := by
    unfold generator
    split <;> simp
  rw [heq, bathLength]
  exact Finset.single_le_sum (fun y _ => abs_nonneg (current i r.up r.down p y))
    (Finset.mem_univ (split i x).2)

private theorem abs_to_uniform_after_bath (i : ι) (r : Rates) (p : Law (Point ι))
    {l : ℝ} (hl : ∀ x, |p.mass x - (dimension ι)⁻¹| ≤ l) (x : Point ι) :
    |(r.apply i p).mass x - (dimension ι)⁻¹| ≤ l + bathLength i r p := by
  have h : (r.apply i p).mass x - (dimension ι)⁻¹ =
      (p.mass x - (dimension ι)⁻¹) + ((r.apply i p).mass x - p.mass x) := by ring
  rw [h]
  exact (abs_add_le _ _).trans (add_le_add (hl x) (bath_coordinate_displacement i r p x))

private def deviation (p : Law (Point ι)) : ℝ :=
  ‖massVector (fun x => p.mass x - (dimension ι)⁻¹)‖

private theorem deviation_uniform : deviation (uniform : Law (Point ι)) = 0 := by
  unfold deviation
  have h : massVector (fun x => (uniform : Law (Point ι)).mass x - (dimension ι)⁻¹) =
      (0 : EuclideanSpace ℝ (Point ι)) := by
    ext x
    simp [massVector, uniform]
  rw [h, norm_zero]

private theorem deviation_permute (e : Equiv.Perm (Point ι)) (p : Law (Point ι)) :
    deviation (permute e p) = deviation p := by
  unfold deviation
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [massVector_norm_sq, massVector_norm_sq]
  congr 1
  exact Equiv.sum_comp e.symm (fun x => (p.mass x - (dimension ι)⁻¹) ^ 2)

private theorem deviation_triangle (p p' : Law (Point ι)) :
    deviation p' ≤ deviation p + ‖massVector (fun x => p'.mass x - p.mass x)‖ := by
  have h : massVector (fun x => p'.mass x - (dimension ι)⁻¹) =
      massVector (fun x => p.mass x - (dimension ι)⁻¹) +
        massVector (fun x => p'.mass x - p.mass x) := by
    ext x
    simp only [PiLp.add_apply, massVector, PiLp.toLp_apply]
    ring
  unfold deviation
  rw [h]
  exact norm_add_le _ _

private theorem scaled_tube (p : Law (Point ι)) {q : ℝ}
    (h : ∀ x, |p.mass x - (dimension ι)⁻¹| ≤ q / dimension ι) (x : Point ι) :
    1 - q ≤ dimension ι * p.mass x ∧ dimension ι * p.mass x ≤ 1 + q := by
  have hd := dimension_pos ι
  have heq : dimension ι * (p.mass x - (dimension ι)⁻¹) = dimension ι * p.mass x - 1 := by
    rw [mul_sub, mul_inv_cancel₀ hd.ne']
  have habs := abs_le.mp (h x)
  have hdiv : dimension ι * (q / dimension ι) = q := by
    field_simp [hd.ne'] <;> ring
  have hlo := mul_le_mul_of_nonneg_left habs.1 hd.le
  have hhi := mul_le_mul_of_nonneg_left habs.2 hd.le
  rw [mul_neg, hdiv, heq] at hlo
  rw [heq, hdiv] at hhi
  exact ⟨by linarith, by linarith⟩

private theorem Protocol.deviation_bound {p : Law (Point ι)} (t : Protocol p)
    {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    ∀ l : ℝ, (∀ x, |p.mass x - (dimension ι)⁻¹| ≤ l) →
      l + t.length ≤ q / dimension ι →
      deviation t.final ≤ deviation p + Real.sqrt
        ((2 * ((1 + q) / (1 - q))) * t.activity * t.entropy) := by
  have hK : 0 ≤ 2 * ((1 + q) / (1 - q)) :=
    mul_nonneg (by norm_num) (div_nonneg (by linarith) (sub_pos.mpr hq₁).le)
  induction t with
  | stop => simp [Protocol.final, Protocol.activity, Protocol.entropy]
  | @gate p e rest ih =>
      intro l hl hwindow
      simpa only [Protocol.final, Protocol.activity, Protocol.entropy, deviation_permute] using
        ih l (fun x => hl (e.symm x)) hwindow
  | bath p i r σ hσ rest ih =>
      intro l hl hwindow
      let K := 2 * ((1 + q) / (1 - q))
      let A := ∑ y, edgeActivity i r.up r.down p y
      let S := ∑ y, σ y
      let dx := ‖massVector (fun x => (r.apply i p).mass x - p.mass x)‖
      let dy := Real.sqrt (K * rest.activity * rest.entropy)
      have hA : 0 ≤ A := Finset.sum_nonneg fun y _ =>
        activity_nonneg i r.up_nonneg r.down_nonneg p y
      have hS : 0 ≤ S := Finset.sum_nonneg fun y _ => (hσ y).1
      have hinput : l ≤ q / dimension ι := by
        change l + (bathLength i r p + rest.length) ≤ _ at hwindow
        linarith [bathLength_nonneg i r p, rest.cost_nonneg.2.2]
      have htube := scaled_tube p (fun x => (hl x).trans hinput)
      have hdx : dx ^ 2 ≤ K * A * S := r.step_bound i hq₀ hq₁ p σ hσ htube
      have hdy : dy ^ 2 ≤ K * rest.activity * rest.entropy :=
        (Real.sq_sqrt (mul_nonneg (mul_nonneg hK rest.cost_nonneg.1)
          rest.cost_nonneg.2.1)).le
      have hsum : (dx + dy) ^ 2 ≤ K * (A + rest.activity) * (S + rest.entropy) := by
        rw [mul_add K]
        exact add_sq_bound (mul_nonneg hK hA) (mul_nonneg hK rest.cost_nonneg.1)
          hS rest.cost_nonneg.2.1 hdx hdy
      have hrest := ih (l + bathLength i r p) (abs_to_uniform_after_bath i r p hl) (by
        simpa only [add_assoc, Protocol.length] using hwindow)
      change deviation rest.final ≤ deviation p +
        Real.sqrt (K * (A + rest.activity) * (S + rest.entropy))
      calc
        _ ≤ deviation (r.apply i p) + dy := hrest
        _ ≤ deviation p + (dx + dy) := by
          rw [← add_assoc]
          exact add_le_add_left (deviation_triangle p (r.apply i p)) dy
        _ ≤ _ := add_le_add_right (Real.le_sqrt_of_sq_le hsum) _

@[simp] private theorem endpoint_bit (i : ι) (b : Bool) (y : Fiber i) :
    endpoint i b y i = b := by
  simp [endpoint, split, Equiv.piSplitAt]

private theorem endpoint_other (i j : ι) (h : j ≠ i) (b : Bool) (y : Fiber i) :
    endpoint i b y j = y ⟨j, h⟩ := by
  simp [endpoint, split, Equiv.piSplitAt, h]

private def coordinateSign (i : ι) : EuclideanSpace ℝ (Point ι) :=
  WithLp.toLp 2 (fun x => sign (x i) / Real.sqrt (dimension ι))

private theorem sign_products (i j : ι) :
    (∑ x : Point ι, sign (x i) * sign (x j)) = if i = j then dimension ι else 0 := by
  by_cases hij : i = j
  · subst j
    have h (x : Point ι) : sign (x i) * sign (x i) = 1 := by
      cases x i <;> norm_num [sign]
    simp [h, dimension, nsmul_eq_mul]
  · rw [if_neg hij, sum_fibers i (fun x => sign (x i) * sign (x j))]
    apply Finset.sum_eq_zero
    intro y _
    cases h : y ⟨j, Ne.symm hij⟩ <;> simp [endpoint_other i j (Ne.symm hij), sign, h]

private theorem coordinate_orthonormal : Orthonormal ℝ (coordinateSign (ι := ι)) := by
  have hd := dimension_pos ι
  have hs : (Real.sqrt (dimension ι)) ^ 2 = dimension ι := Real.sq_sqrt hd.le
  apply orthonormal_iff_ite.mpr
  intro i j
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ x : Point ι, (sign (x j) / Real.sqrt (dimension ι)) *
    star (sign (x i) / Real.sqrt (dimension ι))) = _
  simp only [star_trivial]
  have term (x : Point ι) :
      (sign (x j) / Real.sqrt (dimension ι)) * (sign (x i) / Real.sqrt (dimension ι)) =
        (sign (x j) * sign (x i)) / dimension ι := by
    rw [div_mul_div_comm, ← pow_two, hs]
  simp_rw [term]
  rw [← Finset.sum_div, sign_products j i]
  by_cases hij : i = j
  · simp [hij, hd.ne']
  · simp [hij, Ne.symm hij]

private def halfContrast (p p' : Law (Point ι)) (i : ι) : ℝ :=
  ∑ x, ((p.mass x - p'.mass x) / 2) * sign (x i)

private theorem coordinate_inner (p p' : Law (Point ι)) (i : ι) :
    ⟪coordinateSign i, massVector (fun x => (p.mass x - p'.mass x) / 2)⟫ =
      halfContrast p p' i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ x : Point ι, (Real.sqrt (dimension ι) * ((p.mass x - p'.mass x) / 2)) *
    star (sign (x i) / Real.sqrt (dimension ι))) = _
  unfold halfContrast
  apply Finset.sum_congr rfl
  intro x _
  have hs : Real.sqrt (dimension ι) ≠ 0 := (Real.sqrt_pos.2 (dimension_pos ι)).ne'
  rw [star_trivial]
  field_simp [hs] <;> ring

private def marginal (p : Law (Point ι)) (i : ι) (b : Bool) : ℝ :=
  ∑ y, p.mass (endpoint i b y)

private theorem marginal_add (p : Law (Point ι)) (i : ι) :
    marginal p i false + marginal p i true = 1 := by
  unfold marginal
  rw [← Finset.sum_add_distrib, ← sum_fibers i p.mass, p.normalized]

private theorem halfContrast_eq (p p' : Law (Point ι)) (i : ι) :
    halfContrast p p' i = marginal p i false - marginal p' i false := by
  unfold halfContrast
  rw [sum_fibers i (fun x => ((p.mass x - p'.mass x) / 2) * sign (x i))]
  simp only [endpoint_bit, sign, Bool.false_eq_true, if_false, if_true, mul_one, mul_neg,
    Finset.sum_add_distrib, Finset.sum_neg_distrib, div_eq_mul_inv, ← Finset.sum_mul,
    Finset.sum_sub_distrib]
  change ((marginal p i false - marginal p' i false) * (2 : ℝ)⁻¹) +
    -((marginal p i true - marginal p' i true) * (2 : ℝ)⁻¹) = _
  linarith [marginal_add p i, marginal_add p' i]

/-- Error probability for a deterministic guess of a fair event from one bit.
The two conditional endpoint laws are in the order false, true. -/
def readoutError (p p' : Law (Point ι)) (i : ι) (guess : Bool → Bool) : ℝ :=
  ((∑ x, if guess (x i) then p.mass x else 0) +
    ∑ x, if guess (x i) then 0 else p'.mass x) / 2

private theorem readoutError_eq (p p' : Law (Point ι)) (i : ι) (guess : Bool → Bool) :
    readoutError p p' i guess =
      ((if guess false then marginal p i false else marginal p' i false) +
        if guess true then marginal p i true else marginal p' i true) / 2 := by
  unfold readoutError
  rw [sum_fibers i (fun x => if guess (x i) then p.mass x else 0),
    sum_fibers i (fun x => if guess (x i) then 0 else p'.mass x)]
  cases hf : guess false <;> cases ht : guess true <;>
    simp [hf, ht, marginal, Finset.sum_add_distrib, add_comm]

private theorem margin_of_readout (p p' : Law (Point ι)) (i : ι) (guess : Bool → Bool)
    {m : ℝ} (h : readoutError p p' i guess ≤ (1 - m) / 2) :
    m ≤ |halfContrast p p' i| := by
  rw [halfContrast_eq]
  rw [readoutError_eq] at h
  cases hf : guess false <;> cases ht : guess true
  · simp [hf, ht] at h
    linarith [marginal_add p' i, abs_nonneg (marginal p i false - marginal p' i false)]
  · simp [hf, ht] at h
    linarith [marginal_add p i, le_abs_self (marginal p i false - marginal p' i false)]
  · simp [hf, ht] at h
    linarith [marginal_add p' i, neg_le_abs (marginal p i false - marginal p' i false)]
  · simp [hf, ht] at h
    linarith [marginal_add p i, abs_nonneg (marginal p i false - marginal p' i false)]

private theorem records_bound (p p' : Law (Point ι)) (records : Finset ι)
    {m : ℝ} (hm : 0 ≤ m)
    (hread : ∀ i ∈ records, ∃ guess, readoutError p p' i guess ≤ (1 - m) / 2) :
    (records.card : ℝ) * m ^ 2 ≤
      ‖massVector (fun x => (p.mass x - p'.mass x) / 2)‖ ^ 2 := by
  have hB := coordinate_orthonormal.sum_inner_products_le
    (s := records) (massVector (fun x => (p.mass x - p'.mass x) / 2))
  simp only [coordinate_inner, Real.norm_eq_abs] at hB
  calc
    _ = ∑ _i ∈ records, m ^ 2 := by simp
    _ ≤ ∑ i ∈ records, |halfContrast p p' i| ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨guess, hg⟩ := hread i hi
      exact (sq_le_sq₀ hm (abs_nonneg _)).mpr (margin_of_readout p p' i guess hg)
    _ ≤ _ := hB

private theorem half_difference_bound (p p' : Law (Point ι)) :
    ‖massVector (fun x => (p.mass x - p'.mass x) / 2)‖ ≤
      (deviation p + deviation p') / 2 := by
  have h : massVector (fun x => (p.mass x - p'.mass x) / 2) =
      (1 / 2 : ℝ) • (massVector (fun x => p.mass x - (dimension ι)⁻¹) -
        massVector (fun x => p'.mass x - (dimension ι)⁻¹)) := by
    ext x
    simp only [PiLp.smul_apply, PiLp.sub_apply, massVector, PiLp.toLp_apply, smul_eq_mul]
    ring
  rw [h, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  unfold deviation
  calc
    _ ≤ (1 / 2 : ℝ) * (_ + _) := mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = _ := by ring

/-- The two equiprobable conditional branches contribute separately to each
of the two average costs. -/
def productCost (t₀ t₁ : Protocol (uniform : Law (Point ι))) : ℝ :=
  ((t₀.activity + t₁.activity) / 2) * ((t₀.entropy + t₁.entropy) / 2)

/-- Finite local-bath recording bound. A designated bit is counted when a
readout of that bit attains error at most `(1-m)/2`. Constituent bath steps
have shared rates on their disjoint fibers and carry the local flux premise.
Reversible steps may use arbitrary joint permutations in either branch. For
vanishing product cost on a fixed cube, the prefactor tends to `R / 2`
for `R = records.card`. -/
theorem recording_bound (t₀ t₁ : Protocol (uniform : Law (Point ι))) (records : Finset ι)
    {m : ℝ} (hm : 0 ≤ m)
    (hread : ∀ i ∈ records, ∃ guess, readoutError t₀.final t₁.final i guess ≤ (1 - m) / 2) :
    let C := productCost t₀ t₁
    let q := dimension ι * Real.sqrt (2 * C)
    (records.card : ℝ) * m ^ 2 / 2 * ((1 - q) / (1 + q)) ≤ C := by
  let A := t₀.activity + t₁.activity
  let S := t₀.entropy + t₁.entropy
  let C := productCost t₀ t₁
  let q := dimension ι * Real.sqrt (2 * C)
  change (records.card : ℝ) * m ^ 2 / 2 * ((1 - q) / (1 + q)) ≤ C
  have h₀ := t₀.cost_nonneg
  have h₁ := t₁.cost_nonneg
  have hA : 0 ≤ A := add_nonneg h₀.1 h₁.1
  have hS : 0 ≤ S := add_nonneg h₀.2.1 h₁.2.1
  have hC : 0 ≤ C := mul_nonneg (div_nonneg hA (by norm_num)) (div_nonneg hS (by norm_num))
  have hd := dimension_pos ι
  have hq₀ : 0 ≤ q := mul_nonneg hd.le (Real.sqrt_nonneg _)
  have hqpos : 0 < 1 + q := by linarith
  by_cases hq₁ : q < 1
  · have hbudget (t : Protocol (uniform : Law (Point ι))) (ha : t.activity ≤ A)
        (hs : t.entropy ≤ S) :
        deviation t.final ≤ Real.sqrt ((2 * ((1 + q) / (1 - q))) * t.activity * t.entropy) := by
      have hlen : t.length ^ 2 ≤ 2 * C := by
        calc
          _ ≤ (t.activity / 2) * t.entropy := t.length_sq
          _ ≤ (A / 2) * S := mul_le_mul (div_le_div_of_nonneg_right ha (by norm_num))
            hs t.cost_nonneg.2.1 (div_nonneg hA (by norm_num))
          _ = _ := by change (A / 2) * S = 2 * ((A / 2) * (S / 2)); ring
      have hwidth : 0 + t.length ≤ q / dimension ι := by
        have heq : q / dimension ι = Real.sqrt (2 * C) := by
          dsimp only [q]
          field_simp [hd.ne'] <;> ring
        simpa only [zero_add, heq] using Real.le_sqrt_of_sq_le hlen
      simpa only [deviation_uniform, zero_add] using t.deviation_bound hq₀ hq₁ 0
        (fun x => by simp [uniform]) hwidth
    let K := 2 * ((1 + q) / (1 - q))
    have hK : 0 ≤ K := mul_nonneg (by norm_num) (div_nonneg hqpos.le (sub_pos.mpr hq₁).le)
    have hdev₀ := hbudget t₀ (le_add_of_nonneg_right h₁.1) (le_add_of_nonneg_right h₁.2.1)
    have hdev₁ := hbudget t₁ (le_add_of_nonneg_left h₀.1) (le_add_of_nonneg_left h₀.2.1)
    have hsquare (t : Protocol (uniform : Law (Point ι)))
        (ht : deviation t.final ≤ Real.sqrt (K * t.activity * t.entropy)) :
        deviation t.final ^ 2 ≤ (K * t.activity) * t.entropy := by
      have hh := (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr ht
      rwa [Real.sq_sqrt (mul_nonneg (mul_nonneg hK t.cost_nonneg.1) t.cost_nonneg.2.1)] at hh
    have hsum : (deviation t₀.final + deviation t₁.final) ^ 2 ≤ K * A * S := by
      dsimp only [A, S]
      rw [mul_add K]
      exact add_sq_bound (mul_nonneg hK h₀.1) (mul_nonneg hK h₁.1) h₀.2.1 h₁.2.1
        (hsquare t₀ hdev₀) (hsquare t₁ hdev₁)
    have hhalf := half_difference_bound t₀.final t₁.final
    have hhalf_nonneg : 0 ≤ (deviation t₀.final + deviation t₁.final) / 2 :=
      div_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    have hrec : (records.card : ℝ) * m ^ 2 ≤ K * C := by
      calc
        _ ≤ ‖massVector (fun x => (t₀.final.mass x - t₁.final.mass x) / 2)‖ ^ 2 :=
          records_bound _ _ records hm hread
        _ ≤ ((deviation t₀.final + deviation t₁.final) / 2) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hhalf_nonneg).mpr hhalf
        _ = (deviation t₀.final + deviation t₁.final) ^ 2 / 4 := by ring
        _ ≤ (K * A * S) / 4 := div_le_div_of_nonneg_right hsum (by norm_num)
        _ = _ := by change (K * A * S) / 4 = K * ((A / 2) * (S / 2)); ring
    have hden : 0 < 1 - q := sub_pos.mpr hq₁
    have hscaled : (records.card : ℝ) * m ^ 2 * (1 - q) ≤ C * (2 * (1 + q)) := by
      calc
        _ ≤ (K * C) * (1 - q) := mul_le_mul_of_nonneg_right hrec hden.le
        _ = _ := by dsimp only [K]; field_simp [hden.ne'] <;> ring
    calc
      _ = ((records.card : ℝ) * m ^ 2 * (1 - q)) / (2 * (1 + q)) := by
        field_simp [hqpos.ne'] <;> ring
      _ ≤ C := (div_le_iff₀ (mul_pos (by norm_num) hqpos)).mpr hscaled
  · have hfac : (1 - q) / (1 + q) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_gt hq₁)) hqpos.le
    exact (mul_nonpos_of_nonneg_of_nonpos (by positivity) hfac).trans hC

#print axioms recording_bound

end D5.S3.Quantum.Information.RecordWriting.LocalBathWeakRecording
