/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/TailGeometry
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Legal supported tails and owned intervals control competing scalar orbits. -/

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
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Filter Topology
open scoped Topology

set_option maxHeartbeats 1000000 in
/-- An interval retains its actual endpoint membership. Positive contractions
may approach an excluded fixed endpoint; negative contractions require the
first two actual members and hence the fixed point itself. -/
theorem competing_tail_orbit_criterion (T : Set ℝ) (hT : T.OrdConnected)
    (a y : ℝ) (ha : -1<a) (ha1 : a<1) (hane : a≠0) :
    let F := fun x : ℝ => y+a*(x-y)
    (∀ x, (∀ n : ℕ, F^[n] x ∈ T) ↔
      if 0<a then x∈T ∧ y∈closure T else x∈T ∧ F x∈T) ∧
    ({x : ℝ | ∀ n : ℕ, F^[n] x∈T}.Nonempty ↔
      if 0<a then T.Nonempty ∧ y∈closure T else y∈T) := by
  let F := fun x : ℝ => y+a*(x-y)
  have formula (x : ℝ) (n : ℕ) : F^[n] x = y+a^n*(x-y) := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply',ih,pow_succ]; dsimp [F]; ring
  by_cases apos : 0<a
  · simp only [if_pos apos]
    have criterion (x : ℝ) : (∀ n : ℕ, F^[n] x∈T) ↔ x∈T ∧ y∈closure T := by
      constructor
      · intro orbit
        have conv : Tendsto (fun n : ℕ => F^[n] x) atTop (𝓝 y) := by
          have ht := tendsto_pow_atTop_nhds_zero_of_lt_one apos.le ha1
          simpa only [formula,zero_mul,add_zero] using tendsto_const_nhds.add (ht.mul_const (x-y))
        exact ⟨by simpa using orbit 0,mem_closure_of_tendsto conv (Eventually.of_forall orbit)⟩
      · rintro ⟨hx,hy⟩ n
        cases n with
        | zero => simpa using hx
        | succ n =>
          rw [formula]
          let z := y+a^(n+1)*(x-y)
          have qp : 0<a^(n+1) := pow_pos apos _
          have ql : a^(n+1)<1 := pow_lt_one₀ apos.le ha1 (by omega)
          rcases lt_trichotomy x y with xy | xy | yx
          · have xz : x<z := by
              have hh := mul_pos (sub_pos.mpr ql) (sub_pos.mpr xy)
              dsimp [z]; nlinarith
            have zy : z<y := by
              have hh := mul_pos qp (sub_pos.mpr xy)
              dsimp [z]; nlinarith
            obtain ⟨w,zw,hw⟩ := mem_closure_iff.1 hy (Set.Ioi z) isOpen_Ioi zy
            exact hT.out hx hw ⟨xz.le,zw.le⟩
          · subst x; simpa [z] using hx
          · have yz : y<z := by
              have hh := mul_pos qp (sub_pos.mpr yx)
              dsimp [z]; nlinarith
            have zx : z<x := by
              have hh := mul_pos (sub_pos.mpr ql) (sub_pos.mpr yx)
              dsimp [z]; nlinarith
            obtain ⟨w,wz,hw⟩ := mem_closure_iff.1 hy (Set.Iio z) isOpen_Iio yz
            exact hT.out hw hx ⟨wz.le,zx.le⟩
    refine ⟨criterion,?_⟩
    constructor
    · rintro ⟨x,hx⟩; exact ⟨⟨x,(criterion x).mp hx |>.1⟩,(criterion x).mp hx |>.2⟩
    · rintro ⟨⟨x,hx⟩,hy⟩; exact ⟨x,(criterion x).mpr ⟨hx,hy⟩⟩
  · have aneg : a<0 := lt_of_le_of_ne (le_of_not_gt apos) hane
    simp only [if_neg apos]
    have anti : Antitone F := by
      intro x z hxz
      have hh := mul_le_mul_of_nonpos_left hxz aneg.le
      dsimp [F]; linarith
    have square : a^2≤1 := by nlinarith
    have twice (x : ℝ) : F (F x) = y+a^2*(x-y) := by dsimp [F]; ring
    have middle (x : ℝ) : y∈Set.uIcc x (F x) := by
      by_cases xy : x≤y
      · have hp := mul_nonneg_of_nonpos_of_nonpos aneg.le (sub_nonpos.mpr xy)
        have yf : y≤F x := by dsimp [F]; linarith
        exact ⟨(min_le_left _ _).trans xy,yf.trans (le_max_right _ _)⟩
      · have yx : y≤x := le_of_not_ge xy
        have hp := mul_nonpos_of_nonpos_of_nonneg aneg.le (sub_nonneg.mpr yx)
        have fy : F x≤y := by dsimp [F]; linarith
        exact ⟨(min_le_right _ _).trans fy,yx.trans (le_max_left _ _)⟩
    have invariant (x z : ℝ) (hz : z∈Set.uIcc x (F x)) : F z∈Set.uIcc x (F x) := by
      by_cases xy : x≤y
      · have hp := mul_nonneg_of_nonpos_of_nonpos aneg.le (sub_nonpos.mpr xy)
        have yf : y≤F x := by dsimp [F]; linarith
        have xf : x≤F x := xy.trans yf
        change min x (F x)≤z ∧ z≤max x (F x) at hz
        change min x (F x)≤F z ∧ F z≤max x (F x)
        rw [min_eq_left xf,max_eq_right xf] at hz ⊢
        have hh := mul_le_mul_of_nonpos_right square (sub_nonpos.mpr xy)
        have xx : x≤F (F x) := by rw [twice]; nlinarith
        exact ⟨xx.trans (anti hz.2),anti hz.1⟩
      · have yx : y≤x := le_of_not_ge xy
        have hp := mul_nonpos_of_nonpos_of_nonneg aneg.le (sub_nonneg.mpr yx)
        have fy : F x≤y := by dsimp [F]; linarith
        have fx : F x≤x := fy.trans yx
        change min x (F x)≤z ∧ z≤max x (F x) at hz
        change min x (F x)≤F z ∧ F z≤max x (F x)
        rw [min_eq_right fx,max_eq_left fx] at hz ⊢
        have hh := mul_le_mul_of_nonneg_right square (sub_nonneg.mpr yx)
        have xx : F (F x)≤x := by rw [twice]; nlinarith
        exact ⟨anti hz.2,(anti hz.1).trans xx⟩
    have criterion (x : ℝ) : (∀ n : ℕ, F^[n] x∈T) ↔ x∈T ∧ F x∈T := by
      constructor
      · intro orbit; exact ⟨by simpa using orbit 0,by simpa using orbit 1⟩
      · rintro ⟨hx,hf⟩ n
        apply hT.uIcc_subset hx hf
        induction n with
        | zero => simp
        | succ n ih => rw [Function.iterate_succ_apply']; exact invariant x _ ih
    refine ⟨criterion,?_⟩
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨hx,hf⟩ := (criterion x).mp hx
      exact hT.uIcc_subset hx hf (middle x)
    · intro hy
      refine ⟨y,(criterion y).mpr ⟨hy,?_⟩⟩
      simpa [F] using hy


open scoped Topology
set_option maxHeartbeats 1000000

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open Filter Topology

theorem tail_arithmetic :
    t ^ 2 = 1 - t ∧ 0 < t ∧ t < 1 ∧ 0 < g ∧ g < 1 ∧ 1 < phi := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have htq : t ^ 2 = 1 - t := by dsimp [t]; nlinarith
  have htp : 0 < t := by dsimp [t]; nlinarith
  have ht1 : t < 1 := by dsimp [t]; nlinarith
  have hgp : 0 < g := by dsimp [g, t]; nlinarith
  have hg1 : g < 1 := by dsimp [g]; linarith
  exact ⟨htq, htp, ht1, hgp, hg1, by dsimp [phi]; linarith⟩

/-- Closed branch images cover each literal guard support, including endpoints. -/
private theorem inverse_branch (s : Guard) (z : ℝ) (hz : InSupport s z) :
    ∃ (l : Label) (e : Guard) (z' : ℝ),
      nextGuard s l = some e ∧ InSupport e z' ∧ z = branch l z' := by
  rcases tail_arithmetic with ⟨htq, htp, ht1, hgp, hg1, hphi⟩
  have inverse (l : Label) (e : Guard)
      (hlo : shift l - g * supportUpper e ≤ z)
      (hhi : z ≤ shift l + g) :
      InSupport e ((shift l - z) / g) ∧
        z = branch l ((shift l - z) / g) := by
    refine ⟨⟨(le_div_iff₀ hgp).2 ?_, (div_le_iff₀ hgp).2 ?_⟩, ?_⟩
    · linarith
    · linarith
    · dsimp [branch]
      have hc : g * ((shift l - z) / g) = shift l - z := by
        rw [mul_comm, div_mul_cancel₀ _ (ne_of_gt hgp)]
      rw [hc]
      ring
  rcases hz with ⟨hzlo, hzhi⟩
  cases s with
  | G0 =>
    change z ≤ 1 + t at hzhi
    by_cases h3 : z ≤ t - 1
    · refine ⟨.L3, .G0, (shift .L3 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, phi] <;> nlinarith
    have h3' : t - 1 < z := lt_of_not_ge h3
    by_cases h0 : z ≤ 2 * t - 1
    · refine ⟨.L0, .G0, (shift .L0 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, phi] <;> nlinarith
    have h0' : 2 * t - 1 < z := lt_of_not_ge h0
    by_cases h5 : z ≤ t
    · refine ⟨.L5, .G1, (shift .L5 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, T2] <;> nlinarith
    have h5' : t < z := lt_of_not_ge h5
    by_cases h2 : z ≤ 2 * t
    · refine ⟨.L2, .G0, (shift .L2 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, phi] <;> nlinarith
    have h2' : 2 * t < z := lt_of_not_ge h2
    refine ⟨.L25, .G1, (shift .L25 - z) / g, rfl, ?_⟩
    apply inverse <;> dsimp [shift, supportUpper, g] <;> nlinarith
  | G1 =>
    change z ≤ t at hzhi
    by_cases h3 : z ≤ t - 1
    · refine ⟨.L3, .G0, (shift .L3 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, phi] <;> nlinarith
    have h3' : t - 1 < z := lt_of_not_ge h3
    by_cases h0 : z ≤ 2 * t - 1
    · refine ⟨.L0, .G0, (shift .L0 - z) / g, rfl, ?_⟩
      apply inverse <;> dsimp [shift, supportUpper, g, phi] <;> nlinarith
    have h0' : 2 * t - 1 < z := lt_of_not_ge h0
    refine ⟨.L5, .G1, (shift .L5 - z) / g, rfl, ?_⟩
    apply inverse <;> dsimp [shift, supportUpper, g, T2] <;> nlinarith

/-- One actual legal itinerary realizes every supported scalar, from either guard. -/
theorem lawful_tail (s : Guard) (z : ℝ) (hz : InSupport s z) :
    ∃ (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
      path 0 = s ∧ x 0 = z ∧
      (∀ p, nextGuard (path p) (a p) = some (path (p + 1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = branch (a p) (x (p + 1))) := by
  classical
  let State := {q : Guard × ℝ // InSupport q.1 q.2}
  have progress (q : State) : ∃ (l : Label) (r : State),
      nextGuard q.val.1 l = some r.val.1 ∧ q.val.2 = branch l r.val.2 := by
    obtain ⟨l, e, z', hedge, hsupp, hrec⟩ := inverse_branch q.val.1 q.val.2 q.property
    exact ⟨l, ⟨(e, z'), hsupp⟩, hedge, hrec⟩
  choose label step hedge hrec using progress
  let states : ℕ → State := Nat.rec ⟨(s, z), hz⟩ (fun _ q => step q)
  refine ⟨fun n => label (states n), fun n => (states n).val.2,
    fun n => (states n).val.1, rfl, rfl, ?_, ?_, ?_⟩
  · intro n
    change nextGuard (states n).val.1 (label (states n)) = some (step (states n)).val.1
    exact hedge (states n)
  · intro n
    exact (states n).property
  · intro n
    change (states n).val.2 = branch (label (states n)) (step (states n)).val.2
    exact hrec (states n)

-- The labels are taken from one itinerary, not selected separately for each slot.
private def finiteSegment (a : ℕ → Label) (i : ℕ) : ℕ → List Label
  | 0 => []
  | n + 1 => a i :: finiteSegment a (i + 1) n

private theorem finite_segment_spec
    (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p + 1)))
    (hrec : ∀ p, x p = branch (a p) (x (p + 1))) (n i : ℕ) :
    (finiteSegment a i n).length = n ∧
      LegalWord (path i) (path (i + n)) (finiteSegment a i n) ∧
      x i = compose (finiteSegment a i n) (x (i + n)) := by
  induction n generalizing i with
  | zero => simp [finiteSegment, LegalWord, walk, compose]
  | succ n ih =>
    obtain ⟨hlen, hlegal, hvalue⟩ := ih (i + 1)
    have hi : i + 1 + n = i + (n + 1) := by omega
    refine ⟨by simpa [finiteSegment] using congrArg Nat.succ hlen, ?_, ?_⟩
    · simpa [finiteSegment, LegalWord, walk, hedges i, hi] using hlegal
    · calc
        x i = branch (a i) (x (i + 1)) := hrec i
        _ = branch (a i) (compose (finiteSegment a (i + 1) n) (x (i + (n + 1)))) := by
          rw [hvalue, hi]
        _ = compose (finiteSegment a i (n + 1)) (x (i + (n + 1))) := rfl

/-- Truncation at the actual nth coordinate gives arbitrarily close finite-D scalars. -/
theorem finite_approximation (s : Guard) (z : ℝ) (hz : InSupport s z)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (e : Guard) (w : List Label),
      LegalWord s e w ∧ |z - coordinate w 0| < ε := by
  rcases tail_arithmetic with ⟨htq, htp, ht1, hgp, hg1, hphi⟩
  obtain ⟨a, x, path, hpath0, hx0, hedges, hsupp, hrec⟩ := lawful_tail s z hz
  have hlim : Tendsto (fun n : ℕ => phi * g ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hgp.le hg1).const_mul phi
  obtain ⟨n, hn⟩ := (Filter.Tendsto.eventually_lt_const hε hlim).exists
  have segment := finite_segment_spec a x path hedges hrec n 0
  simp only [Nat.zero_add, hpath0, hx0] at segment
  have affine := literal_source_geometry.2.2.2.1 (finiteSegment a 0 n) 0 (x n)
  rw [zero_add, segment.1] at affine
  have hd : z - compose (finiteSegment a 0 n) 0 = (-g) ^ n * x n := by
    have hv := segment.2.2.trans affine
    linarith
  have hu : supportUpper (path n) ≤ phi := by
    cases path n <;> dsimp [supportUpper, phi] <;> linarith
  have hxbound : |x n| ≤ phi := abs_le.mpr
    ⟨by linarith [(hsupp n).1], (hsupp n).2.trans hu⟩
  refine ⟨path n, finiteSegment a 0 n, segment.2.1, ?_⟩
  change |z - compose (finiteSegment a 0 n) 0| < ε
  calc
    |z - compose (finiteSegment a 0 n) 0| = |(-g) ^ n * x n| := congrArg abs hd
    _ = g ^ n * |x n| := by rw [abs_mul, abs_pow, abs_neg, abs_of_pos hgp]
    _ ≤ g ^ n * phi := mul_le_mul_of_nonneg_left hxbound (pow_nonneg hgp.le n)
    _ = phi * g ^ n := mul_comm _ _
    _ < ε := hn

/-- One finite legal tail is chosen in the hull interior, with its entire literal path. -/
theorem finite_tail_interior (s : Guard) (lo hi : ℝ) (hlt : lo < hi)
    (hsupport : ∀ z ∈ Set.Icc lo hi, InSupport s z) :
    ∃ (e : Guard) (w : List Label), LegalWord s e w ∧
      lo < coordinate w 0 ∧ coordinate w 0 < hi ∧
      OperationFiniteSource (address w) ∧
      ∃ path : ℕ → Guard, path 0 = s ∧
        (∀ p, nextGuard (path p) (address w p) = some (path (p + 1))) ∧
        (∀ p, InSupport (path p) (coordinate w p)) ∧
        (∀ p, coordinate w p = branch (address w p) (coordinate w (p + 1))) := by
  have hm : InSupport s ((lo + hi) / 2) :=
    hsupport _ ⟨by linarith, by linarith⟩
  obtain ⟨e, w, hw, herror⟩ :=
    finite_approximation s ((lo + hi) / 2) hm ((hi - lo) / 2) (by linarith)
  have herr := abs_lt.mp herror
  refine ⟨e, w, hw, by linarith [herr.2], by linarith [herr.1], ?_,
    literal_address_path s e w hw⟩
  refine ⟨w.length, ?_⟩
  intro p hp
  simp only [address, List.getElem?_eq_none hp, Option.getD_none]

/-- A legal finite prefix splices the same guard/coordinate tail into an actual source.
The last prefix recurrence and both exact shifted futures are part of the conclusion. -/
theorem prepend_legal_tail
    (s e : Guard) (w : List Label) (hw : LegalWord s e w)
    (a : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard)
    (hpath0 : path 0 = e)
    (hedges : ∀ p, nextGuard (path p) (a p) = some (path (p + 1)))
    (hsupp : ∀ p, InSupport (path p) (x p))
    (hrec : ∀ p, x p = branch (a p) (x (p + 1))) :
    ∃ (b : ℕ → Label) (y : ℕ → ℝ) (q : ℕ → Guard),
      q 0 = s ∧ y 0 = compose w (x 0) ∧
      (∀ p, nextGuard (q p) (b p) = some (q (p + 1))) ∧
      (∀ p, InSupport (q p) (y p)) ∧
      (∀ p, y p = branch (b p) (y (p + 1))) ∧
      (∀ p (hp : p < w.length), b p = w[p]) ∧
      (∀ p, b (w.length + p) = a p) ∧
      (∀ p, y (w.length + p) = x p) := by
  induction w generalizing s with
  | nil =>
    have he : s = e := by simpa [LegalWord, walk] using hw
    refine ⟨a, x, path, hpath0.trans he.symm, rfl, hedges, hsupp, hrec, ?_, ?_, ?_⟩
    · intro p hp
      simp at hp
    · intro p
      simp only [List.length_nil, Nat.zero_add]
    · intro p
      simp only [List.length_nil, Nat.zero_add]
  | cons l w ih =>
    cases hn : nextGuard s l with
    | none => simp [LegalWord, walk, hn] at hw
    | some s' =>
      have hw' : LegalWord s' e w := by simpa [LegalWord, walk, hn] using hw
      obtain ⟨b, y, q, hq0, hy0, hbedges, hbSupp, hbRec, hbPrefix, hbFuture, hyFuture⟩ :=
        ih s' hw'
      refine ⟨(fun p => match p with | 0 => l | n + 1 => b n),
        (fun p => match p with | 0 => compose (l :: w) (x 0) | n + 1 => y n),
        (fun p => match p with | 0 => s | n + 1 => q n),
        rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro p
        cases p with
        | zero => simpa only [hq0] using hn
        | succ p => exact hbedges p
      · intro p
        cases p with
        | zero =>
          exact literal_source_geometry.1 s e (l :: w) (x 0) hw
            (by simpa only [hpath0] using hsupp 0)
        | succ p => exact hbSupp p
      · intro p
        cases p with
        | zero => simpa only [compose, hy0]
        | succ p => exact hbRec p
      · intro p hp
        cases p with
        | zero => rfl
        | succ p =>
          have hp' : p < w.length := by simpa only [List.length_cons, Nat.succ_lt_succ_iff] using hp
          simpa only [List.getElem_cons_succ] using hbPrefix p hp'
      · intro p
        simpa only [List.length_cons, Nat.succ_add] using hbFuture p
      · intro p
        simpa only [List.length_cons, Nat.succ_add] using hyFuture p




open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open Filter Topology

/-- Actual cell endpoint ownership, with both outside support endpoints included. -/
def lowerOwned (o : Ownership) (c : Color) : Prop :=
  match c.val with
  | 0 => True | 1 => o 0 = true | 2 => o 1 = true
  | 3 => o 2 = true | 4 => o 3 = true | _ => o 4 = true

def upperOwned (o : Ownership) (c : Color) : Prop :=
  match c.val with
  | 0 => o 0 = false | 1 => o 1 = false | 2 => o 2 = false
  | 3 => o 3 = false | 4 => o 4 = false | _ => True

def FlagInterval (lo hi : ℝ) (left right : Prop) (z : ℝ) : Prop :=
  lo ≤ z ∧ z ≤ hi ∧ (z = lo → left) ∧ (z = hi → right)

private theorem cut_chain :
    cut 0 < cut 1 ∧ cut 1 < cut 2 ∧ cut 2 < cut 3 ∧
    cut 3 < cut 4 ∧ cut 4 < cut 5 ∧ cut 5 < cut 6 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have htlo : (3 : ℝ) / 5 < t := by dsimp [t]; nlinarith
  have hthi : t < (2 : ℝ) / 3 := by dsimp [t]; nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [cut, lam, T2, phi, g] <;> linarith

theorem cut_bounds (c : Color) :
    -1 ≤ cut c.val ∧ cut c.val < cut (c.val + 1) ∧ cut (c.val + 1) ≤ phi := by
  rcases cut_chain with ⟨h01, h12, h23, h34, h45, h56⟩
  fin_cases c <;> norm_num [cut] at *
  all_goals repeat' constructor
  all_goals linarith

/-- Exact cell membership retains the original endpoint ownership. -/
theorem cell_flag_interval (o : Ownership) (c : Color) (u : ℝ) :
    Cell o c u ↔ FlagInterval (cut c.val) (cut (c.val + 1))
      (lowerOwned o c) (upperOwned o c) u := by
  rcases cut_chain with ⟨h01, h12, h23, h34, h45, h56⟩
  fin_cases c <;>
    simp only [Cell, InSupport, supportUpper, FlagInterval, lowerOwned, upperOwned,
      readout, ite_eq_iff]
  all_goals norm_num [cut] at *
  all_goals aesop
  all_goals try linarith
  all_goals try tauto
  all_goals by_cases heq1 : u = -T2 - lam <;> try (simp_all <;> linarith)
  all_goals by_cases heq2 : u = g - 3*lam <;> try (simp_all <;> linarith)
  all_goals by_cases heq3 : u = t - 5*lam <;> try (simp_all <;> linarith)
  all_goals by_cases heq4 : u = 2*t - 7*lam <;> try (simp_all <;> linarith)
  all_goals by_cases heq5 : u = 2*t + lam <;> try (simp_all <;> linarith)
  all_goals simp_all
  all_goals first | (apply lt_of_le_of_ne <;> assumption) | linarith

/-- Closed-budget dilation retains exactly the two original endpoint flags.
The zero-budget branch chooses u=z and does not demand a strict error bound. -/
private theorem flag_dilation (lo hi θ z : ℝ) (left right : Prop)
    (hwidth : lo < hi) (hθ : 0 ≤ θ) :
    (∃ u, FlagInterval lo hi left right u ∧ |z - u| ≤ θ) ↔
      FlagInterval (lo - θ) (hi + θ) left right z := by
  constructor
  · rintro ⟨u, hu, he⟩
    obtain ⟨hel, her⟩ := abs_le.mp he
    refine ⟨by linarith [hu.1], by linarith [hu.2.1], ?_, ?_⟩
    · intro hz
      exact hu.2.2.1 (by linarith [hu.1])
    · intro hz
      exact hu.2.2.2 (by linarith [hu.2.1])
  · intro hz
    by_cases hzero : θ = 0
    · subst θ
      refine ⟨z, ?_, by simp⟩
      simpa only [sub_zero, add_zero] using hz
    have hθpos : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hzero)
    by_cases hleft : z = lo - θ
    · refine ⟨lo, ⟨le_rfl, hwidth.le, fun _ => hz.2.2.1 hleft, ?_⟩, ?_⟩
      · intro heq
        linarith
      · rw [hleft]
        have : lo - θ - lo = -θ := by ring
        rw [this, abs_neg, abs_of_nonneg hθ]
    by_cases hright : z = hi + θ
    · refine ⟨hi, ⟨hwidth.le, le_rfl, ?_, fun _ => hz.2.2.2 hright⟩, ?_⟩
      · intro heq
        linarith
      · rw [hright]
        have : hi + θ - hi = θ := by ring
        rw [this, abs_of_nonneg hθ]
    have hzlo : lo - θ < z := lt_of_le_of_ne hz.1 (Ne.symm hleft)
    have hzhi : z < hi + θ := lt_of_le_of_ne hz.2.1 hright
    have overlap : max lo (z - θ) < min hi (z + θ) := by
      rw [max_lt_iff, lt_min_iff, lt_min_iff]
      exact ⟨⟨hwidth, by linarith⟩, ⟨by linarith, by linarith⟩⟩
    obtain ⟨u, hlu, huh⟩ := exists_between overlap
    have ulo : lo < u := lt_of_le_of_lt (le_max_left _ _) hlu
    have uhi : u < hi := lt_of_lt_of_le huh (min_le_left _ _)
    have eu : z - θ < u := lt_of_le_of_lt (le_max_right _ _) hlu
    have ue : u < z + θ := lt_of_lt_of_le huh (min_le_right _ _)
    exact ⟨u, ⟨ulo.le, uhi.le, by intro heq; linarith, by intro heq; linarith⟩,
      abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-- The actual, supported color-attainable set, not the closed relaxation. -/
def OwnedColor (o : Ownership) (θ : ℝ) (c : Color) (z : ℝ) : Prop :=
  InSupport .G0 z ∧ ∃ u, Cell o c u ∧ |z - u| ≤ θ

theorem owned_color_interval (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (c : Color) (z : ℝ) :
    OwnedColor o θ c z ↔ InSupport .G0 z ∧
      FlagInterval (cut c.val - θ) (cut (c.val + 1) + θ)
        (lowerOwned o c) (upperOwned o c) z := by
  unfold OwnedColor
  simp_rw [cell_flag_interval]
  rw [flag_dilation _ _ _ _ _ _ (cut_bounds c).2.1 hθ]

private theorem clip_fixes (z : ℝ) (hz : InSupport .G0 z) : clip z = z := by
  change -1 ≤ z ∧ z ≤ phi at hz
  simp only [clip, min_eq_right hz.2, max_eq_right hz.1]

private theorem clip_support (z : ℝ) : InSupport .G0 (clip z) := by
  have hphi : (-1 : ℝ) ≤ phi := (cut_bounds 0).1.trans (cut_bounds 0).2.1.le |>.trans (cut_bounds 0).2.2
  exact ⟨le_max_left _ _, max_le hphi (min_le_left _ _)⟩

private theorem clip_error (z e : ℝ) (hz : InSupport .G0 z) :
    |z - clip (z + e)| ≤ |e| := by
  change -1 ≤ z ∧ z ≤ phi at hz
  by_cases hlo : z + e ≤ -1
  · have hhi : z + e ≤ phi := hlo.trans (hz.1.trans hz.2)
    have he : e ≤ 0 := by linarith [hz.1]
    have habs : 0 ≤ z - (-1) := by linarith [hz.1]
    rw [clip, min_eq_right hhi, max_eq_left hlo, abs_of_nonneg habs, abs_of_nonpos he]
    linarith
  by_cases hhi : phi ≤ z + e
  · have hs : (-1 : ℝ) ≤ phi := hz.1.trans hz.2
    have he : 0 ≤ e := by linarith [hz.2]
    have habs : z - phi ≤ 0 := by linarith [hz.2]
    rw [clip, min_eq_left hhi, max_eq_right hs, abs_of_nonpos habs, abs_of_nonneg he]
    linarith
  have hlo' : -1 ≤ z + e := (lt_of_not_ge hlo).le
  have hhi' : z + e ≤ phi := (lt_of_not_ge hhi).le
  rw [clip, min_eq_right hhi', max_eq_right hlo']
  have : z - (z + e) = -e := by ring
  rw [this, abs_neg]

theorem owned_color_error (o : Ownership) (θ : ℝ) (c : Color)
    (z : ℝ) (hz : InSupport .G0 z) :
    OwnedColor o θ c z ↔ ∃ e : ℝ, |e| ≤ θ ∧ observe o z e = c := by
  constructor
  · rintro ⟨_, u, hu, he⟩
    refine ⟨u - z, by simpa only [abs_sub_comm] using he, ?_⟩
    have hsum : z + (u - z) = u := by ring
    simpa only [observe, hsum, clip_fixes u hu.1] using hu.2
  · rintro ⟨e, he, hread⟩
    exact ⟨hz, clip (z + e), ⟨clip_support _, hread⟩, (clip_error z e hz).trans he⟩

private theorem flag_ordConnected (lo hi : ℝ) (left right : Prop) :
    {z | FlagInterval lo hi left right z}.OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  refine ⟨hx.1.trans hz.1, hz.2.trans hy.2.1, ?_, ?_⟩
  · intro hzl
    exact hx.2.2.1 (by linarith [hx.1, hz.1])
  · intro hzh
    exact hy.2.2.2 (by linarith [hy.2.1, hz.2])

theorem owned_color_ordConnected (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ) (c : Color) :
    {z | OwnedColor o θ c z}.OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  obtain ⟨hxs, hxf⟩ := (owned_color_interval o θ hθ c x).mp hx
  obtain ⟨hys, hyf⟩ := (owned_color_interval o θ hθ c y).mp hy
  exact (owned_color_interval o θ hθ c z).mpr
    ⟨⟨hxs.1.trans hz.1, hz.2.trans hys.2⟩,
      (flag_ordConnected _ _ _ _).out hxf hyf hz⟩

private theorem suffix_preimage_ordConnected (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (c : Color) (w : List Label) : {z | OwnedColor o θ c (compose w z)}.OrdConnected := by
  have affine (z : ℝ) : compose w z = compose w 0 + (-g) ^ w.length * z := by
    simpa only [zero_add] using literal_source_geometry.2.2.2.1 w 0 z
  by_cases hsign : 0 ≤ (-g) ^ w.length
  · apply (owned_color_ordConnected o θ hθ c).preimage_mono
    intro x y hxy
    rw [affine x, affine y]
    linarith [mul_le_mul_of_nonneg_left hxy hsign]
  · apply (owned_color_ordConnected o θ hθ c).preimage_anti
    intro x y hxy
    rw [affine x, affine y]
    linarith [mul_le_mul_of_nonpos_left hxy (le_of_not_ge hsign)]

/-- The finite competing-tail set: every stem suffix and both return-color choices.
Only departures r<length are tested. There is no extra terminal color condition. -/
def CompetingT (o : Ownership) (θ : ℝ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color) : Set ℝ :=
  {z | InSupport s z ∧
    (∀ r (hr : r < h.length), OwnedColor o θ h[r] (compose (Q.drop r) z)) ∧
    (∀ i r (hr : r < (W i).length), OwnedColor o θ (W i)[r] (compose (V.drop r) z))}

theorem competingT_ordConnected (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s : Guard) (Q V : List Label) (h : List Color) (W : Bool → List Color) :
    (CompetingT o θ s Q V h W).OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  refine ⟨⟨hx.1.1.trans hz.1, hz.2.trans hy.1.2⟩, ?_, ?_⟩
  · intro r hr
    exact (suffix_preimage_ordConnected o θ hθ h[r] (Q.drop r)).out
      (hx.2.1 r hr) (hy.2.1 r hr) hz
  · intro i r hr
    exact (suffix_preimage_ordConnected o θ hθ (W i)[r] (V.drop r)).out
      (hx.2.2 i r hr) (hy.2.2 i r hr) hz

private theorem support_embed (s : Guard) (z : ℝ) (hz : InSupport s z) :
    InSupport .G0 z := by
  have hu : supportUpper s ≤ phi := by cases s <;> dsimp [supportUpper, phi] <;> linarith
  exact ⟨hz.1, hz.2.trans hu⟩

theorem suffix_supported (s e : Guard) (w : List Label)
    (hw : LegalWord s e w) (z : ℝ) (hz : InSupport e z) (p : ℕ) :
    InSupport .G0 (compose (w.drop p) z) := by
  induction w generalizing s p with
  | nil => simpa [compose] using support_embed e z hz
  | cons l w ih =>
    cases p with
    | zero => exact support_embed s _ (literal_source_geometry.1 s e (l :: w) z hw hz)
    | succ p =>
      cases hn : nextGuard s l with
      | none => simp [LegalWord, walk, hn] at hw
      | some s' =>
        have hw' : LegalWord s' e w := by simpa [LegalWord, walk, hn] using hw
        simpa only [List.drop_succ_cons] using ih s' hw' p

/-- Concrete T is exactly the supported scalar with all actual Q and both W slot tests. -/
theorem competingT_mem_actual (o : Ownership) (θ : ℝ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V) (z : ℝ) :
    z ∈ CompetingT o θ s Q V h W ↔ InSupport s z ∧
      BlockSupply o θ false Q h z ∧ ∀ i, BlockSupply o θ false V (W i) z := by
  constructor
  · intro hz
    refine ⟨hz.1, ?_, ?_⟩
    · intro r hr
      have hc := hz.2.1 r hr
      simpa only [Bool.false_eq_true, if_false] using (owned_color_error o θ h[r] _ hc.1).mp hc
    · intro i r hr
      have hc := hz.2.2 i r hr
      simpa only [Bool.false_eq_true, if_false] using (owned_color_error o θ (W i)[r] _ hc.1).mp hc
  · rintro ⟨hz, stem, returns⟩
    refine ⟨hz, ?_, ?_⟩
    · intro r hr
      apply (owned_color_error o θ h[r] _ (suffix_supported .G0 s Q hQ z hz r)).mpr
      simpa only [Bool.false_eq_true, if_false] using stem r hr
    · intro i r hr
      apply (owned_color_error o θ (W i)[r] _ (suffix_supported s s V hV z hz r)).mpr
      simpa only [Bool.false_eq_true, if_false] using returns i r hr




open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource

/-- The closed relaxation intersects the actual coordinate support. -/
def ClosedExpanded (θ : ℝ) (c : Color) (z : ℝ) : Prop :=
  InSupport .G0 z ∧ cut c.val - θ ≤ z ∧ z ≤ cut (c.val + 1) + θ

theorem expanded_distance_formula (θ : ℝ) (hθ : 0 ≤ θ) (c : Color) (z : ℝ) :
    ClosedExpanded θ c z ↔ InSupport .G0 z ∧
      max (cut c.val-z) (max 0 (z-cut (c.val+1))) ≤ θ := by
  simp only [ClosedExpanded,max_le_iff]
  constructor
  · rintro ⟨hs,hlo,hhi⟩
    exact ⟨hs,by linarith,hθ,by linarith⟩
  · rintro ⟨hs,hlo,_,hhi⟩
    exact ⟨hs,by linarith,by linarith⟩

/-- Two actual numeric endpoint costs at every observed departure suffix. -/
def EndpointCertificate (θ : ℝ) (lo hi : ℝ) (w : List Label) (cs : List Color) : Prop :=
  ∀ r (hr : r < cs.length),
    (InSupport .G0 (compose (w.drop r) lo) ∧
      max (cut cs[r].val-compose (w.drop r) lo)
        (max 0 (compose (w.drop r) lo-cut (cs[r].val+1))) ≤ θ) ∧
    (InSupport .G0 (compose (w.drop r) hi) ∧
      max (cut cs[r].val-compose (w.drop r) hi)
        (max 0 (compose (w.drop r) hi-cut (cs[r].val+1))) ≤ θ)

private theorem literal_slope_ne_zero (w : List Label) : (-g) ^ w.length ≠ 0 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have hsn := Real.sqrt_nonneg (5 : ℝ)
  have hgp : 0 < g := by dsimp [g, t]; nlinarith
  exact pow_ne_zero _ (neg_ne_zero.mpr (ne_of_gt hgp))

theorem compose_strict_inside (w : List Label) (lo hi x left right : ℝ)
    (hxlo : lo < x) (hxhi : x < hi)
    (hlo : left ≤ compose w lo ∧ compose w lo ≤ right)
    (hhi : left ≤ compose w hi ∧ compose w hi ≤ right) :
    left < compose w x ∧ compose w x < right := by
  have affine (z : ℝ) : compose w z = compose w 0 + (-g) ^ w.length * z := by
    simpa only [zero_add] using literal_source_geometry.2.2.2.1 w 0 z
  have hne := literal_slope_ne_zero w
  by_cases hpos : 0 < (-g) ^ w.length
  · have hxl : compose w lo < compose w x := by
      rw [affine lo, affine x]
      nlinarith [mul_pos hpos (sub_pos.mpr hxlo)]
    have hxh : compose w x < compose w hi := by
      rw [affine x, affine hi]
      nlinarith [mul_pos hpos (sub_pos.mpr hxhi)]
    exact ⟨lt_of_le_of_lt hlo.1 hxl, lt_of_lt_of_le hxh hhi.2⟩
  · have hneg : (-g) ^ w.length < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
    have hxl : compose w hi < compose w x := by
      rw [affine hi, affine x]
      nlinarith [mul_neg_of_neg_of_pos hneg (sub_pos.mpr hxhi)]
    have hxh : compose w x < compose w lo := by
      rw [affine x, affine lo]
      nlinarith [mul_neg_of_neg_of_pos hneg (sub_pos.mpr hxlo)]
    exact ⟨lt_of_le_of_lt hhi.1 hxl, lt_of_lt_of_le hxh hlo.2⟩

/-- Finite endpoint data gives actual readout witnesses at every departure, at theta itself. -/
theorem certificate_actual_slots (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (lo hi : ℝ) (w : List Label) (cs : List Color)
    (cert : EndpointCertificate θ lo hi w cs)
    (x : ℝ) (hxlo : lo < x) (hxhi : x < hi) :
    BlockSupply o θ false w cs x := by
  intro r hr
  obtain ⟨hleft, hright⟩ := cert r hr
  have hl := (expanded_distance_formula θ hθ cs[r] _).mpr hleft
  have hh := (expanded_distance_formula θ hθ cs[r] _).mpr hright
  have supported := compose_strict_inside (w.drop r) lo hi x (-1) phi hxlo hxhi hl.1 hh.1
  have expanded := compose_strict_inside (w.drop r) lo hi x
    (cut cs[r].val - θ) (cut (cs[r].val + 1) + θ) hxlo hxhi hl.2 hh.2
  have hs : InSupport .G0 (compose (w.drop r) x) := ⟨supported.1.le, supported.2.le⟩
  have actual : OwnedColor o θ cs[r] (compose (w.drop r) x) :=
    (owned_color_interval o θ hθ cs[r] _).mpr
      ⟨hs, expanded.1.le, expanded.2.le,
        by intro heq; linarith [expanded.1], by intro heq; linarith [expanded.2]⟩
  simpa only [Bool.false_eq_true, if_false] using
    (owned_color_error o θ cs[r] _ hs).mp actual

theorem block_supply_append (o : Ownership) (θ : ℝ)
    (u v : List Label) (cu cv : List Color) (hlen : u.length = cu.length) (z : ℝ)
    (hu : BlockSupply o θ false u cu (compose v z))
    (hv : BlockSupply o θ false v cv z) :
    BlockSupply o θ false (u ++ v) (cu ++ cv) z := by
  intro r hr
  by_cases hp : r < cu.length
  · have hp' : r ≤ u.length := by omega
    simpa only [List.getElem_append_left hp, List.drop_append_of_le_length hp',
      literal_source_geometry.2.2.2.2] using hu r hp
  · have hle : u.length ≤ r := by omega
    have hr' : r - cu.length < cv.length := by
      simp only [List.length_append] at hr
      omega
    have value := hv (r - cu.length) hr'
    simpa only [List.getElem_append_right (le_of_not_gt hp), List.drop_append,
      List.drop_eq_nil_of_le hle, List.nil_append, hlen] using value


end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
