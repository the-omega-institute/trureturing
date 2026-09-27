/- GID: D5/S3/TotalVariation/ParryBilateralLaw
   generality: I
   mirror-B: D5/B/S3/TotalVariation/ParryBilateralLaw
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual bilateral Parry source and joint signed stationary path law. -/

import D5.S3.TotalVariation.ParryResetLaw
import D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open D5.S3.Estimation.DataProcessing.InverseLimitEventTotalVariation
open D5.S3.Estimation.DataProcessing.InverseLimitProbabilityExtension
open D5.S3.TotalVariation.TwistedResetPaths
open D5.S3.TotalVariation.ParryResetLaw

namespace D5.S3.TotalVariation.ParryBilateralLaw

/-- Every block of `k` consecutive relation bits contains a zero. -/
def Admissible (k : ℕ) (r : ℤ → Bool) : Prop :=
  ∀ t : ℤ, ∃ i : Fin k, r (t + i.val) = false

/-- The actual bilateral forbidden-one-run relation space. -/
abbrev RelationPath (k : ℕ) := {r : ℤ → Bool // Admissible k r}

/-- Paths all of whose edges have positive mass under the actual Parry kernel. -/
abbrev ResetPath (k : ℕ) :=
  {x : ℤ → State k // ∀ t, 0 < kernel k (parryParameter k) (x t) (x (t + 1))}

/-- Finite XOR, in the indicated order, including the specified starting sign. -/
def xorWalk (b : Bool) (c : ℕ → Bool) : ℕ → Bool
  | 0 => b
  | n + 1 => xor (xorWalk b c n) (c n)

/-- Reconstruction from the sign at zero, using finite XOR in both time directions. -/
def signAt (b : Bool) (r : ℤ → Bool) : ℤ → Bool
  | .ofNat n => xorWalk b (fun i => !r (i : ℤ)) n
  | .negSucc n => xorWalk b (fun i => !r (-(i : ℤ) - 1)) (n + 1)

/-- The edge relation read from consecutive absolute signs. -/
def readRelation {k : ℕ} (x : ℤ → State k) (t : ℤ) : Bool :=
  !(xor (x t).1 (x (t + 1)).1)

/-- The bilateral left shift on the actual relation space. -/
def relationShift {k : ℕ} (r : RelationPath k) : RelationPath k :=
  ⟨fun t => r.val (t + 1), fun t => by
    obtain ⟨i, hi⟩ := r.property (t + 1)
    exact ⟨i, by simpa only [show t + (i.val : ℤ) + 1 = t + 1 + i.val by omega] using hi⟩⟩

/-- The actual bilateral coding is a measurable bijection onto positive-kernel
paths. Its suffix is determined by the entire relation path (in fact by at most
`k` past bits), its inverse reads the origin sign and every edge relation, and
it intertwines the anchored skew shift with the path shift. -/
theorem bilateral_reset_coding (k : ℕ) (hk : 2 ≤ k) :
    ∃ e : (Bool × RelationPath k) ≃ᵐ ResetPath k,
      (∀ (b : Bool) (r : RelationPath k) (t : ℤ),
        ((e (b, r)).val t).1 = signAt b r.val t) ∧
      (∀ (z : Bool × RelationPath k) (t : ℤ),
        let j := ((e z).val t).2.val
        z.2.val (t - (j : ℤ) - 1) = false ∧
        ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true) ∧
      (∀ x : ResetPath k,
        (e.symm x).1 = (x.val 0).1 ∧ (e.symm x).2.val = readRelation x.val) ∧
      (∀ z : Bool × RelationPath k,
        (e (xor z.1 (!z.2.val 0), relationShift z.2)).val =
          fun t => (e z).val (t + 1)) := by
  classical
  have pastZero (r : RelationPath k) (t : ℤ) :
      ∃ n : ℕ, r.val (t - (n : ℤ) - 1) = false := by
    obtain ⟨i, hi⟩ := r.property (t - k)
    refine ⟨k - i.val - 1, ?_⟩
    have he : t - ((k - i.val - 1 : ℕ) : ℤ) - 1 = t - k + i.val := by
      have := i.isLt
      omega
    simpa only [he] using hi
  let suffix (r : RelationPath k) (t : ℤ) : Fin k :=
    ⟨Nat.find (pastZero r t), by
      obtain ⟨i, hi⟩ := r.property (t - k)
      have hz : r.val (t - ((k - i.val - 1 : ℕ) : ℤ) - 1) = false := by
        have he : t - ((k - i.val - 1 : ℕ) : ℤ) - 1 = t - k + i.val := by
          have := i.isLt
          omega
        simpa only [he] using hi
      have hle := Nat.find_min' (pastZero r t) hz
      have := i.isLt
      omega⟩
  have suffix_spec (r : RelationPath k) (t : ℤ) :
      r.val (t - ((suffix r t).val : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < (suffix r t).val → r.val (t - (i : ℤ) - 1) = true := by
    refine ⟨Nat.find_spec (pastZero r t), ?_⟩
    intro i hi
    have hn := Nat.find_min (pastZero r t) hi
    cases h : r.val (t - (i : ℤ) - 1) <;> simp_all
  have suffix_unique (r : RelationPath k) (t : ℤ) (n : ℕ)
      (hz : r.val (t - (n : ℤ) - 1) = false)
      (ho : ∀ i : ℕ, i < n → r.val (t - (i : ℤ) - 1) = true) :
      (suffix r t).val = n := by
    apply (Nat.find_eq_iff (pastZero r t)).2
    exact ⟨hz, fun i hi => by rw [ho i hi]; decide⟩
  have suffix_step (r : RelationPath k) (t : ℤ) :
      (suffix r (t + 1)).val =
        if r.val t then (suffix r t).val + 1 else 0 := by
    cases ht : r.val t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      apply suffix_unique
      · simpa using ht
      · intro i hi; omega
    · simp only [↓reduceIte]
      apply suffix_unique
      · simpa only [show t + 1 - (((suffix r t).val + 1 : ℕ) : ℤ) - 1 =
            t - ((suffix r t).val : ℤ) - 1 by omega] using (suffix_spec r t).1
      · intro i hi
        rcases i with _ | i
        · simpa using ht
        · simpa only [show t + 1 - ((i + 1 : ℕ) : ℤ) - 1 = t - (i : ℤ) - 1 by omega]
            using (suffix_spec r t).2 i (by omega)
  have suffix_measurable (t : ℤ) : Measurable (fun r : RelationPath k => suffix r t) := by
    have hm : Measurable (fun r : RelationPath k => Nat.find (pastZero r t)) := by
      apply measurable_find
      intro n
      have he : Measurable (fun r : RelationPath k => r.val (t - (n : ℤ) - 1)) :=
        (measurable_pi_apply _).comp measurable_subtype_coe
      exact he (measurableSet_singleton false)
    apply measurable_to_countable
    intro r
    simpa only [Set.preimage, Set.mem_singleton_iff, Fin.ext_iff] using
      hm (measurableSet_singleton (suffix r t).val)
  have walk_measurable (c : ℕ → (Bool × RelationPath k) → Bool)
      (hc : ∀ n, Measurable (c n)) (n : ℕ) :
      Measurable (fun z : Bool × RelationPath k => xorWalk z.1 (fun i => c i z) n) := by
    induction n with
    | zero => exact measurable_fst
    | succ n ih =>
      exact (measurable_of_countable (fun p : Bool × Bool => xor p.1 p.2)).comp
        (ih.prodMk (hc n))
  have sign_measurable (t : ℤ) :
      Measurable (fun z : Bool × RelationPath k => signAt z.1 z.2.val t) := by
    cases t with
    | ofNat n =>
      apply walk_measurable
      intro i
      exact (measurable_from_top (f := Bool.not)).comp
        ((measurable_pi_apply _).comp (measurable_subtype_coe.comp measurable_snd))
    | negSucc n =>
      apply walk_measurable
      intro i
      exact (measurable_from_top (f := Bool.not)).comp
        ((measurable_pi_apply _).comp (measurable_subtype_coe.comp measurable_snd))
  have sign_zero (b : Bool) (r : ℤ → Bool) : signAt b r 0 = b := rfl
  have sign_step (b : Bool) (r : ℤ → Bool) (t : ℤ) :
      signAt b r (t + 1) = xor (signAt b r t) (!r t) := by
    cases t with
    | ofNat n => rfl
    | negSucc n =>
      cases n with
      | zero => simp [signAt, xorWalk]
      | succ n =>
        have he : Int.negSucc (n + 1) + 1 = Int.negSucc n := by omega
        rw [he]
        simp only [signAt, xorWalk]
        have he' : (-(↑(n + 1) : ℤ) - 1) = Int.negSucc (n + 1) := by omega
        rw [he']
        simp
  have sign_unique (b : Bool) (r : ℤ → Bool) (a : ℤ → Bool)
      (h0 : a 0 = b) (hs : ∀ t, a (t + 1) = xor (a t) (!r t)) :
      a = signAt b r := by
    funext t
    induction t using Int.induction_on with
    | zero => exact h0
    | succ n ih => rw [hs, ih, sign_step]
    | pred n ih =>
      have hh := hs (-(n : ℤ) - 1)
      have hh' := sign_step b r (-(n : ℤ) - 1)
      simp only [sub_add_cancel] at hh hh'
      rw [ih, hh'] at hh
      exact Bool.xor_left_inj.mp hh.symm
  have hp : 0 < parryParameter k := by
    have h := (parry_stationary_law k hk).1.1
    linarith
  have hweight (j : Fin k) : 0 < suffixWeight k (parryParameter k) j :=
    lt_of_lt_of_le hp ((parry_stationary_law k hk).2.1 j).1
  have edge (s t : State k) :
      0 < kernel k (parryParameter k) s t ↔
        (t.1 = !s.1 ∧ t.2.val = 0) ∨
        (t.1 = s.1 ∧ t.2.val = s.2.val + 1) := by
    unfold kernel
    split_ifs with h0 h1
    · exact ⟨fun _ => Or.inl h0, fun _ => div_pos hp (hweight _)⟩
    · exact ⟨fun _ => Or.inr h1, fun _ => div_pos (mul_pos hp (hweight _)) (hweight _)⟩
    · simp_all
  let code (z : Bool × RelationPath k) : ResetPath k :=
    ⟨fun t => (signAt z.1 z.2.val t, suffix z.2 t), fun t => by
      apply (edge _ _).2
      dsimp only
      rw [sign_step]
      have ht := suffix_step z.2 t
      cases h : z.2.val t
      · left
        exact ⟨by simp, by simpa [h] using ht⟩
      · right
        exact ⟨by simp, by simpa [h] using ht⟩⟩
  have code_measurable : Measurable code := by
    apply Measurable.subtype_mk
    exact measurable_pi_lambda _ fun t =>
      (sign_measurable t).prodMk ((suffix_measurable t).comp measurable_snd)
  have path_step (x : ResetPath k) (t : ℤ) :
      ((readRelation x.val t = false) ∧ (x.val (t + 1)).2.val = 0) ∨
      ((readRelation x.val t = true) ∧
        (x.val (t + 1)).2.val = (x.val t).2.val + 1) := by
    rcases (edge _ _).1 (x.property t) with h | h
    · left
      refine ⟨?_, h.2⟩
      simp [readRelation, h.1]
    · right
      exact ⟨by simp [readRelation, h.1], h.2⟩
  have path_suffix (x : ResetPath k) (t : ℤ) :
      readRelation x.val (t - ((x.val t).2.val : ℤ) - 1) = false ∧
      ∀ i : ℕ, i < (x.val t).2.val → readRelation x.val (t - (i : ℤ) - 1) = true := by
    have descend : ∀ i : ℕ, i ≤ (x.val t).2.val →
        (x.val (t - (i : ℤ))).2.val + i = (x.val t).2.val := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        intro hi
        have hi' := ih (by omega)
        have hs := path_step x (t - (i : ℤ) - 1)
        have he : t - (i : ℤ) - 1 + 1 = t - (i : ℤ) := by omega
        rw [he] at hs
        rcases hs with h | h
        · omega
        · have he' : t - ((i + 1 : ℕ) : ℤ) = t - (i : ℤ) - 1 := by omega
          rw [he']
          omega
    constructor
    · have hd := descend (x.val t).2.val le_rfl
      have hs := path_step x (t - ((x.val t).2.val : ℤ) - 1)
      have he : t - ((x.val t).2.val : ℤ) - 1 + 1 = t - ((x.val t).2.val : ℤ) := by omega
      rw [he] at hs
      rcases hs with h | h
      · exact h.1
      · omega
    · intro i hi
      have hd := descend i (by omega)
      have hs := path_step x (t - (i : ℤ) - 1)
      have he : t - (i : ℤ) - 1 + 1 = t - (i : ℤ) := by omega
      rw [he] at hs
      rcases hs with h | h
      · omega
      · exact h.1
  have path_admissible (x : ResetPath k) : Admissible k (readRelation x.val) := by
    intro t
    let j := (x.val (t + k)).2
    refine ⟨⟨k - j.val - 1, by have := j.isLt; omega⟩, ?_⟩
    have he : t + ((k - j.val - 1 : ℕ) : ℤ) = t + k - (j.val : ℤ) - 1 := by
      have := j.isLt
      omega
    simpa only [he] using (path_suffix x (t + k)).1
  let decode (x : ResetPath k) : Bool × RelationPath k :=
    ((x.val 0).1, ⟨readRelation x.val, path_admissible x⟩)
  have decode_measurable : Measurable decode := by
    apply Measurable.prodMk
    · exact measurable_fst.comp ((measurable_pi_apply 0).comp measurable_subtype_coe)
    · apply Measurable.subtype_mk
      apply measurable_pi_lambda
      intro t
      exact (measurable_of_countable (fun p : Bool × Bool => !(xor p.1 p.2))).comp
        ((measurable_fst.comp ((measurable_pi_apply t).comp measurable_subtype_coe)).prodMk
          (measurable_fst.comp ((measurable_pi_apply (t + 1)).comp measurable_subtype_coe)))
  have left_inv : Function.LeftInverse decode code := by
    intro z
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      funext t
      dsimp [decode, code, readRelation]
      rw [sign_step]
      simp
  have right_inv : Function.RightInverse decode code := by
    intro x
    apply Subtype.ext
    funext t
    apply Prod.ext
    · have hu := sign_unique (x.val 0).1 (readRelation x.val) (fun s => (x.val s).1) rfl
        (fun s => by simp [readRelation])
      exact (congrFun hu t).symm
    · apply Fin.ext
      exact suffix_unique (decode x).2 t (x.val t).2.val
        (path_suffix x t).1 (path_suffix x t).2
  let e : (Bool × RelationPath k) ≃ᵐ ResetPath k :=
    { toFun := code, invFun := decode, left_inv := left_inv, right_inv := right_inv,
      measurable_toFun := code_measurable, measurable_invFun := decode_measurable }
  refine ⟨e, fun _ _ _ => rfl, fun z t => suffix_spec z.2 t, fun _ => ⟨rfl, rfl⟩, ?_⟩
  intro z
  funext t
  apply Prod.ext
  · have hu := sign_unique (xor z.1 (!z.2.val 0)) (relationShift z.2).val
      (fun s => signAt z.1 z.2.val (s + 1))
      (by simpa only [sign_zero] using sign_step z.1 z.2.val 0)
      (fun s => sign_step z.1 z.2.val (s + 1))
    exact (congrFun hu t).symm
  · apply Fin.ext
    apply suffix_unique
    · change z.2.val (t - ((suffix z.2 (t + 1)).val : ℤ) - 1 + 1) = false
      simpa only [show t - ((suffix z.2 (t + 1)).val : ℤ) - 1 + 1 =
        t + 1 - ((suffix z.2 (t + 1)).val : ℤ) - 1 by omega] using (suffix_spec z.2 (t + 1)).1
    · intro i hi
      change z.2.val (t - (i : ℤ) - 1 + 1) = true
      simpa only [show t - (i : ℤ) - 1 + 1 = t + 1 - (i : ℤ) - 1 by omega]
        using (suffix_spec z.2 (t + 1)).2 i hi

/-- The fair sign anchor, as a probability measure on the two signs. -/
noncomputable def fairAnchor : Measure Bool :=
  (PMF.ofFintype (fun _ : Bool => (1 / 2 : ℝ≥0∞))
    (by norm_num [ENNReal.mul_inv_cancel])).toMeasure

/-- Stationary mass of the unsigned suffix immediately before a relation bit. -/
noncomputable def suffixLaw (k : ℕ) (j : Fin k) : ℝ :=
  parryParameter k ^ j.val * suffixWeight k (parryParameter k) j / normalizer k

/-- The source suffix-chain kernel: a zero resets, and a one increments. -/
noncomputable def suffixKernel (k : ℕ) (j h : Fin k) : ℝ :=
  if h.val = 0 then parryParameter k / suffixWeight k (parryParameter k) j
  else if h.val = j.val + 1 then
    parryParameter k * suffixWeight k (parryParameter k) h /
      suffixWeight k (parryParameter k) j
  else 0

/-- The stationary bilateral Parry source and its signed path law. The source
is identified by its actual suffix cylinders, and the coding transports its
product with an independent fair sign to the signed Markov law. Both cylinder
formulas include every integer origin, zero transitions, and forbidden words. -/
theorem bilateral_parry_law (k : ℕ) (hk : 2 ≤ k) :
    ∃ (e : (Bool × RelationPath k) ≃ᵐ ResetPath k)
      (μ : ProbabilityMeasure (RelationPath k)) (ν : ProbabilityMeasure (ℤ → State k)),
      (∀ (b : Bool) (r : RelationPath k) (t : ℤ),
        ((e (b, r)).val t).1 = signAt b r.val t) ∧
      (∀ (z : Bool × RelationPath k) (t : ℤ),
        let j := ((e z).val t).2.val
        z.2.val (t - (j : ℤ) - 1) = false ∧
        ∀ i : ℕ, i < j → z.2.val (t - (i : ℤ) - 1) = true) ∧
      (∀ x : ResetPath k,
        (e.symm x).1 = (x.val 0).1 ∧ (e.symm x).2.val = readRelation x.val) ∧
      (∀ z : Bool × RelationPath k,
        (e (xor z.1 (!z.2.val 0), relationShift z.2)).val =
          fun t => (e z).val (t + 1)) ∧
      (μ : Measure (RelationPath k)).map relationShift = μ ∧
      (ν : Measure (ℤ → State k)).map (fun x t => x (t + 1)) = ν ∧
      (fairAnchor.prod (μ : Measure (RelationPath k))).map
        (fun z => (e z).val) = ν ∧
      (∀ (ell : ℤ) (m : ℕ) (w : Fin (m + 1) → State k),
        (ν : Measure (ℤ → State k))
          {x | (fun i : Fin (m + 1) => x (ell + i.val)) = w} =
          ENNReal.ofReal (parryLaw k (w 0) * ∏ i : Fin m,
            kernel k (parryParameter k) (w i.castSucc) (w i.succ))) ∧
      (∀ (ell : ℤ) (m : ℕ) (v : Fin (m + 1) → Fin k),
        (μ : Measure (RelationPath k))
          {r | (fun i : Fin (m + 1) => ((e (false, r)).val (ell + i.val)).2) = v} =
          ENNReal.ofReal (suffixLaw k (v 0)) * ∏ i : Fin m,
            ENNReal.ofReal (suffixKernel k (v i.castSucc) (v i.succ))) := by
  classical
  let : NeZero k := ⟨by omega⟩
  let π : State k → ℝ≥0∞ := fun s => ENNReal.ofReal (parryLaw k s)
  let Q : State k → State k → ℝ≥0∞ := fun s t =>
    ENNReal.ofReal (kernel k (parryParameter k) s t)
  obtain ⟨_, _, _, hQ, hrow, hπ, hnorm, hstat, hflip⟩ := parry_stationary_law k hk
  have π_sum : ∑ s, π s = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => hπ s), hnorm]
    simp
  have Q_sum (s : State k) : ∑ t, Q s t = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun t _ => hQ s t), hrow]
    simp
  have Q_stationary (t : State k) : ∑ s, π s * Q s t = π t := by
    simp_rw [π, Q, ← ENNReal.ofReal_mul (hπ _)]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun s _ => mul_nonneg (hπ s) (hQ s t)), hstat]
  let mass (n : ℕ) (w : Fin (n + 1) → State k) : ℝ≥0∞ :=
    π (w 0) * ∏ i : Fin n, Q (w i.castSucc) (w i.succ)
  have mass_cons (n : ℕ) (s : State k) (w : Fin (n + 1) → State k) :
      mass (n + 1) (Fin.cons s w) =
        π s * Q s (w 0) * ∏ i : Fin n, Q (w i.castSucc) (w i.succ) := by
    simp [mass, Fin.prod_univ_succ, mul_assoc]
  have mass_snoc (n : ℕ) (s : State k) (w : Fin (n + 1) → State k) :
      mass (n + 1) (Fin.snoc w s) = mass n w * Q (w (Fin.last n)) s := by
    simp [mass, Fin.prod_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last,
      -Fin.castSucc_succ, Fin.succ_castSucc, mul_assoc]
  have sum_cons (n : ℕ) (w : Fin (n + 1) → State k) :
      ∑ s, mass (n + 1) (Fin.cons s w) = mass n w := by
    simp_rw [mass_cons]
    rw [← Finset.sum_mul, Q_stationary]
  have sum_snoc (n : ℕ) (w : Fin (n + 1) → State k) :
      ∑ s, mass (n + 1) (Fin.snoc w s) = mass n w := by
    simp_rw [mass_snoc]
    rw [← Finset.mul_sum, Q_sum, mul_one]
  have mass_sum (n : ℕ) : ∑ w, mass n w = 1 := by
    induction n with
    | zero =>
      simpa [mass] using ((Equiv.funUnique (Fin 1) (State k)).sum_comp π).trans π_sum
    | succ n ih =>
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 2) => State k)]
      rw [Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk]
      rw [Finset.sum_comm]
      simp_rw [sum_cons]
      exact ih
  let pLaw (n : ℕ) : PMF (Fin (n + 1) → State k) := PMF.ofFintype (mass n) (mass_sum n)
  have tail_law (n : ℕ) : (pLaw (n + 1)).map Fin.tail = pLaw n := by
    ext w
    rw [PMF.map_apply, tsum_fintype,
      ← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 2) => State k)]
    rw [Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk,
      Fin.tail_cons, pLaw, PMF.ofFintype_apply]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact sum_cons n w
  have init_law (n : ℕ) : (pLaw (n + 1)).map Fin.init = pLaw n := by
    ext w
    rw [PMF.map_apply, tsum_fintype,
      ← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (n + 2) => State k)]
    rw [Fintype.sum_prod_type]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk,
      Fin.init_snoc, pLaw, PMF.ofFintype_apply]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact sum_snoc n w
  let crop (N a n : ℕ) (h : a + n ≤ N) (w : Fin (N + 1) → State k) :
      Fin (n + 1) → State k := fun i => w ⟨a + i.val, by omega⟩
  have crop_law (N a n : ℕ) (h : a + n ≤ N) :
      (pLaw N).map (crop N a n h) = pLaw n := by
    induction N generalizing a n with
    | zero =>
      have ha : a = 0 := by omega
      have hn : n = 0 := by omega
      subst a n
      have he : crop 0 0 0 h = id := by
        funext w i
        dsimp [crop]
        congr 1
        exact Fin.ext (Nat.zero_add _)
      rw [he, PMF.map_id]
    | succ N ih =>
      rcases a with _ | a
      · by_cases hn : n = N + 1
        · subst n
          have he : crop (N + 1) 0 (N + 1) h = id := by
            funext w i
            dsimp [crop]
            congr 1
            exact Fin.ext (Nat.zero_add _)
          rw [he, PMF.map_id]
        · have hn' : 0 + n ≤ N := by omega
          have he : crop (N + 1) 0 n h = crop N 0 n hn' ∘ Fin.init := by
            funext w i
            rfl
          rw [he, ← PMF.map_comp, init_law]
          exact ih 0 n hn'
      · have ha : a + n ≤ N := by omega
        have he : crop (N + 1) (a + 1) n h = crop N a n ha ∘ Fin.tail := by
          funext w i
          dsimp [crop, Fin.tail]
          congr 1
          apply Fin.ext
          dsimp
          omega
        rw [he, ← PMF.map_comp, tail_law]
        exact ih a n ha
  let unsignedKernel : Fin k → Fin k → ℝ := suffixKernel k
  let U (j h : Fin k) : ℝ≥0∞ := ENNReal.ofReal (unsignedKernel j h)
  let πu (j : Fin k) : ℝ≥0∞ := ENNReal.ofReal (suffixLaw k j)
  have sumQ (a : Bool) (j h : Fin k) : ∑ b : Bool, Q (a,j) (b,h) = U j h := by
    by_cases h0 : h.val = 0
    · cases a <;> simp [Q, U, unsignedKernel, suffixKernel, kernel, h0, -Fin.val_eq_zero_iff]
    · by_cases h1 : h.val = j.val + 1
      · cases a <;> simp [Q, U, unsignedKernel, suffixKernel, kernel, h1, -Fin.val_eq_zero_iff]
      · cases a <;> simp [Q, U, unsignedKernel, suffixKernel, kernel, h0, h1, -Fin.val_eq_zero_iff]
  have sumπ (j : Fin k) : ∑ a : Bool, π (a,j) = πu j := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hπ (a,j))]
    congr 1
    simp only [parryLaw, suffixLaw]
    rw [Fintype.sum_bool]
    ring
  have signs_sum (n : ℕ) (v : Fin (n + 1) → Fin k) (a : Bool) :
      (∑ b : Fin n → Bool, ∏ i : Fin n,
        Q ((Fin.cons a b : Fin (n + 1) → Bool) i.castSucc, v i.castSucc)
          ((Fin.cons a b : Fin (n + 1) → Bool) i.succ, v i.succ)) =
        ∏ i : Fin n, U (v i.castSucc) (v i.succ) := by
    induction n generalizing a with
    | zero => simp
    | succ n ih =>
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => Bool), Fintype.sum_prod_type]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero,
        Fin.cons_succ, Fin.castSucc_zero, Fin.castSucc_succ]
      have he (b : Bool) :
          (∑ c : Fin n → Bool, Q (a, v 0) (b, v (Fin.succ 0)) *
            ∏ i : Fin n, Q ((Fin.cons b c : Fin (n + 1) → Bool) i.castSucc, v i.castSucc.succ)
              (c i, v i.succ.succ)) =
          Q (a, v 0) (b, v (Fin.succ 0)) * ∏ i : Fin n, U (v i.castSucc.succ) (v i.succ.succ) := by
        rw [← Finset.mul_sum]
        congr 1
        exact ih (Fin.tail v) b
      simp_rw [he]
      rw [← Finset.sum_mul, sumQ]
  have unsigned_block_mass (n : ℕ) (v : Fin (n + 1) → Fin k) :
      ((pLaw n).map (fun w i => (w i).2)) v =
        πu (v 0) * ∏ i : Fin n, U (v i.castSucc) (v i.succ) := by
    rw [PMF.map_apply, tsum_fintype,
      ← Equiv.sum_comp (Equiv.arrowProdEquivProdArrow
        (Fin (n + 1)) (fun _ => Bool) (fun _ => Fin k)).symm,
      Fintype.sum_prod_type]
    simp only [Equiv.arrowProdEquivProdArrow_symm_apply,
      pLaw, PMF.ofFintype_apply]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => Bool), Fintype.sum_prod_type]
    simp only [Fin.consEquiv, Equiv.coe_fn_mk, mass,
      Equiv.arrowProdEquivProdArrow_symm_apply, Fin.cons_zero]
    simp_rw [← Finset.mul_sum, signs_sum]
    rw [← Finset.sum_mul, sumπ]
  let B (l : ℕ) := Fin (2 * l + 1) → State k
  let bond (l : ℕ) (w : B (l + 1)) : B l := fun i => w ⟨i.val + 1, by omega⟩
  have bond_surjective (l : ℕ) : Function.Surjective (bond l) := by
    intro w
    refine ⟨fun i => w ⟨min (i.val - 1) (2 * l), by omega⟩, ?_⟩
    funext i
    dsimp [bond]
    congr 1
    apply Fin.ext
    dsimp
    have := i.isLt
    omega
  let finiteLaw (n : ℕ) : ProbabilityMeasure (Fin (n + 1) → State k) :=
    ⟨(pLaw n).toMeasure, inferInstance⟩
  let laws (l : ℕ) : ProbabilityMeasure (Fin 1 → B l) :=
    (finiteLaw (2 * l)).map (measurable_of_countable (fun w _ => w)).aemeasurable
  have laws_compatible (l : ℕ) :
      (laws (l + 1) : Measure (Fin 1 → B (l + 1))).map (fun y j => bond l (y j)) =
        (laws l : Measure (Fin 1 → B l)) := by
    change (((pLaw (2 * (l + 1))).toMeasure).map (fun w _ => w)).map
      (fun y j => bond l (y j)) = ((pLaw (2 * l)).toMeasure).map (fun w _ => w)
    rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    have hb : bond l = crop (2 * (l + 1)) 1 (2 * l) (by omega) := by
      funext w i
      dsimp [bond, crop]
      congr 1
      apply Fin.ext
      dsimp
      omega
    have hc := congrArg PMF.toMeasure (crop_law (2 * (l + 1)) 1 (2 * l) (by omega))
    rw [← PMF.toMeasure_map _ _ (measurable_of_countable _), ← hb] at hc
    rw [← hc, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    rfl
  obtain ⟨threadLaw, hthread, unique_thread⟩ :=
    exists_unique_probability_extension bond bond_surjective 1 laws laws_compatible
  let T := Thread B bond
  have descend (x : T) (l m : ℕ) (h : l ≤ m) (i : Fin (2 * l + 1)) :
      x.val m ⟨i.val + (m - l), by omega⟩ = x.val l i := by
    induction h with
    | refl => simp
    | @step m h ih =>
      have hlm : l ≤ m := h
      have hstep := congrFun (x.property m) (⟨i.val + (m - l), by omega⟩ : Fin (2 * m + 1))
      dsimp [bond] at hstep
      rw [← ih, ← hstep]
      change x.val (m + 1) _ = x.val (m + 1) _
      apply congrArg (x.val (m + 1))
      apply Fin.ext
      dsimp
      omega
  let unpack (x : T) (t : ℤ) : State k :=
    x.val t.natAbs ⟨(t + t.natAbs).toNat, by
      have h1 := Int.natCast_natAbs t
      have h2 := (Int.le_natAbs (a := t))
      have h3 : -t ≤ (t.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -t))
      omega⟩
  have unpack_measurable : Measurable unpack := by
    apply measurable_pi_lambda
    intro t
    exact (measurable_pi_apply _).comp ((measurable_pi_apply _).comp measurable_subtype_coe)
  have unpack_block (x : T) (l : ℕ) (i : Fin (2 * l + 1)) :
      unpack x ((i.val : ℤ) - l) = x.val l i := by
    let t : ℤ := (i.val : ℤ) - l
    let m := max l t.natAbs
    have h1 := descend x t.natAbs m (Nat.le_max_right _ _) ⟨(t + t.natAbs).toNat, by
      have := (Int.le_natAbs (a := t))
      have : -t ≤ (t.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -t))
      omega⟩
    have h2 := descend x l m (Nat.le_max_left _ _) i
    change x.val t.natAbs _ = x.val l i
    rw [← h1, ← h2]
    apply congrArg (x.val m)
    apply Fin.ext
    dsimp
    have : -t ≤ (t.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -t))
    have hm1 : l ≤ m := Nat.le_max_left _ _
    have hm2 : t.natAbs ≤ m := Nat.le_max_right _ _
    dsimp [t] at *
    omega
  let ν : ProbabilityMeasure (ℤ → State k) :=
    threadLaw.map (unpack_measurable.comp (measurable_pi_apply 0)).aemeasurable
  have ν_center (l : ℕ) :
      (ν : Measure (ℤ → State k)).map (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) =
        (pLaw (2 * l)).toMeasure := by
    change ((threadLaw : Measure (Fin 1 → T)).map (fun z => unpack (z 0))).map _ = _
    rw [Measure.map_map (f := fun z : Fin 1 → T => unpack (z 0))
      (by fun_prop) (by exact unpack_measurable.comp (measurable_pi_apply 0))]
    have he : (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) ∘
        (fun z : Fin 1 → T => unpack (z 0)) =
        (fun w : Fin 1 → B l => w 0) ∘ levelProjection bond 1 l := by
      funext z i
      exact unpack_block (z 0) l i
    rw [he, ← Measure.map_map (f := levelProjection bond 1 l)
      (by fun_prop) (by
        exact measurable_pi_lambda _ fun j =>
          (measurable_pi_apply l).comp
            (measurable_subtype_coe.comp (measurable_pi_apply j))), hthread]
    change (((pLaw (2 * l)).toMeasure).map (fun w (_ : Fin 1) => w)).map
      (fun w : Fin 1 → B l => w 0) = _
    rw [Measure.map_map (by fun_prop) (measurable_of_countable _)]
    exact Measure.map_id
  have ν_block (ell : ℤ) (n : ℕ) :
      (ν : Measure (ℤ → State k)).map (fun x (i : Fin (n + 1)) => x (ell + i.val)) =
        (pLaw n).toMeasure := by
    let l := ell.natAbs + n
    have hel := (Int.le_natAbs (a := ell))
    have heg : -ell ≤ (ell.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -ell))
    have ha : (ell + l).toNat + n ≤ 2 * l := by dsimp [l]; omega
    have he : (fun x : ℤ → State k => fun i : Fin (n + 1) => x (ell + i.val)) =
        crop (2 * l) (ell + l).toNat n ha ∘
          (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) := by
      funext x i
      dsimp [crop]
      congr 1
      dsimp [l]
      omega
    rw [he, ← Measure.map_map (measurable_of_countable _) (by fun_prop), ν_center,
      PMF.toMeasure_map _ _ (measurable_of_countable _)]
    exact congrArg PMF.toMeasure (crop_law (2 * l) (ell + l).toNat n ha)
  let pack (x : ℤ → State k) : Fin 1 → T := fun _ =>
    ⟨fun l i => x ((i.val : ℤ) - l), fun l => by
      funext i
      dsimp [bond]
      congr 1
      omega⟩
  have pack_measurable : Measurable pack := by
    dsimp [pack]
    fun_prop
  have unpack_pack (x : ℤ → State k) : unpack (pack x 0) = x := by
    funext t
    dsimp [pack, unpack]
    congr 1
    have hneg : -t ≤ (t.natAbs : ℤ) := by simpa using (Int.le_natAbs (a := -t))
    omega
  have ν_unique (ρ : ProbabilityMeasure (ℤ → State k))
      (hρ : ∀ l, (ρ : Measure (ℤ → State k)).map
        (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) =
        (pLaw (2 * l)).toMeasure) : ρ = ν := by
    have hu : ρ.map pack_measurable.aemeasurable = threadLaw := by
      apply unique_thread
      intro l
      change ((ρ : Measure (ℤ → State k)).map pack).map (levelProjection bond 1 l) = _
      rw [Measure.map_map (by
        exact measurable_pi_lambda _ fun j =>
          (measurable_pi_apply l).comp
            (measurable_subtype_coe.comp (measurable_pi_apply j))) pack_measurable]
      have he : levelProjection bond 1 l ∘ pack =
          (fun w (_ : Fin 1) => w) ∘
            (fun x : ℤ → State k => fun i : Fin (2 * l + 1) => x ((i.val : ℤ) - l)) := rfl
      rw [he, ← Measure.map_map (measurable_of_countable _) (by fun_prop), hρ]
      rfl
    have he := congrArg (fun ζ : ProbabilityMeasure (Fin 1 → T) =>
      (ζ : Measure (Fin 1 → T)).map (fun z => unpack (z 0))) hu
    change (((ρ : Measure (ℤ → State k)).map pack).map (fun z => unpack (z 0))) =
      (ν : Measure (ℤ → State k)) at he
    rw [Measure.map_map (by exact unpack_measurable.comp (measurable_pi_apply 0))
      pack_measurable] at he
    have hid : (fun z : Fin 1 → T => unpack (z 0)) ∘ pack = id := funext unpack_pack
    rw [hid, Measure.map_id] at he
    exact ProbabilityMeasure.toMeasure_injective he
  clear_value ν
  have flip_kernel (s t : State k) :
      Q (TwistedResetPaths.flip s) (TwistedResetPaths.flip t) = Q s t := by
    rcases s with ⟨a, j⟩
    rcases t with ⟨b, h⟩
    cases a <;> cases b <;> simp [Q, kernel, TwistedResetPaths.flip]
  have mass_flip (n : ℕ) (w : Fin (n + 1) → State k) :
      mass n (fun i => TwistedResetPaths.flip (w i)) = mass n w := by
    simp only [mass, flip_kernel]
    rw [show π (TwistedResetPaths.flip (w 0)) = π (w 0) by dsimp [π]; rw [hflip]]
  have pLaw_flip (n : ℕ) : (pLaw n).map (fun w i => TwistedResetPaths.flip (w i)) = pLaw n := by
    let e : (Fin (n + 1) → State k) ≃ (Fin (n + 1) → State k) :=
      { toFun := fun w i => TwistedResetPaths.flip (w i),
        invFun := fun w i => TwistedResetPaths.flip (w i),
        left_inv := by intro w; funext i; simp [TwistedResetPaths.flip],
        right_inv := by intro w; funext i; simp [TwistedResetPaths.flip] }
    ext w
    rw [PMF.map_apply, tsum_fintype, ← Equiv.sum_comp e]
    have ff (s : State k) : TwistedResetPaths.flip (TwistedResetPaths.flip s) = s := by
      simp [TwistedResetPaths.flip]
    simp only [e, Equiv.coe_fn_mk, pLaw, PMF.ofFintype_apply, ff, mass_flip]
    simp
  let flipPath (x : ℤ → State k) : ℤ → State k := fun t => TwistedResetPaths.flip (x t)
  have flip_measurable : Measurable flipPath := by
    apply measurable_pi_lambda
    intro t
    exact (measurable_of_countable TwistedResetPaths.flip).comp (measurable_pi_apply t)
  have ν_flip : (ν : Measure (ℤ → State k)).map flipPath = ν := by
    have hu := ν_unique (ν.map flip_measurable.aemeasurable) (fun l => by
      change ((ν : Measure (ℤ → State k)).map flipPath).map _ = _
      rw [Measure.map_map (by fun_prop) flip_measurable]
      have he : (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) ∘ flipPath =
          (fun w i => TwistedResetPaths.flip (w i)) ∘
            (fun x : ℤ → State k => fun i : Fin (2 * l + 1) => x ((i.val : ℤ) - l)) := rfl
      rw [he, ← Measure.map_map (measurable_of_countable _) (by fun_prop), ν_center,
        PMF.toMeasure_map _ _ (measurable_of_countable _), pLaw_flip])
    exact congrArg ProbabilityMeasure.toMeasure hu
  have ν_supported : ∀ᵐ x ∂(ν : Measure (ℤ → State k)),
      ∀ t, 0 < kernel k (parryParameter k) (x t) (x (t + 1)) := by
    rw [ae_all_iff]
    intro t
    rw [ae_iff]
    let bad : Set (Fin 2 → State k) := {w | ¬0 < kernel k (parryParameter k) (w 0) (w 1)}
    have hb : MeasurableSet bad := Set.toFinite bad |>.measurableSet
    have hz : (pLaw 1).toMeasure bad = 0 := by
      rw [PMF.toMeasure_apply_fintype]
      apply Finset.sum_eq_zero
      intro w _
      by_cases h : w ∈ bad
      · have hzero : kernel k (parryParameter k) (w 0) (w 1) = 0 :=
          le_antisymm (le_of_not_gt h) (hQ _ _)
        simp [Set.indicator_of_mem h, pLaw, mass, Q, hzero]
      · simp [Set.indicator_of_notMem h]
    have he := congrArg (fun μ : Measure (Fin 2 → State k) => μ bad) (ν_block t 1)
    rw [Measure.map_apply (by fun_prop) hb, hz] at he
    simpa [bad, Set.preimage] using he
  have pLaw_mass (n : ℕ) (w : Fin (n + 1) → State k) :
      pLaw n w = mass n w := rfl
  clear_value pLaw
  have support_measurable : MeasurableSet
      {x : ℤ → State k | ∀ t, 0 < kernel k (parryParameter k) (x t) (x (t + 1))} := by
    simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro t
    have hpair : Measurable (fun x : ℤ → State k => (x t, x (t + 1))) :=
      (measurable_pi_apply t).prodMk (measurable_pi_apply (t + 1))
    have hm : Measurable (fun x : ℤ → State k =>
        kernel k (parryParameter k) (x t) (x (t + 1))) := by
      exact (measurable_of_countable (fun p : State k × State k =>
        kernel k (parryParameter k) p.1 p.2)).comp hpair
    exact hm measurableSet_Ioi
  have sub_embedding : MeasurableEmbedding (Subtype.val : ResetPath k → ℤ → State k) :=
    MeasurableEmbedding.subtype_coe support_measurable
  have support_range : ∀ᵐ x ∂(ν : Measure (ℤ → State k)),
      x ∈ Set.range (Subtype.val : ResetPath k → ℤ → State k) := by
    simpa using ν_supported
  let νS : ProbabilityMeasure (ResetPath k) :=
    ⟨(ν : Measure (ℤ → State k)).comap Subtype.val,
      sub_embedding.isProbabilityMeasure_comap support_range⟩
  have νS_map : (νS : Measure (ResetPath k)).map Subtype.val = ν := by
    exact (sub_embedding.map_comap _).trans (Measure.restrict_eq_self_of_ae_mem support_range)
  obtain ⟨e, esign, esuffix, eread, eshift⟩ := bilateral_reset_coding k hk
  let F (z : Bool × RelationPath k) := (e z).val
  have Fmeas : Measurable F := measurable_subtype_coe.comp e.measurable
  have Fembedding : MeasurableEmbedding F := sub_embedding.comp e.measurableEmbedding
  let ρ : ProbabilityMeasure (Bool × RelationPath k) := νS.map e.symm.measurable.aemeasurable
  have ρ_map : (ρ : Measure (Bool × RelationPath k)).map F = ν := by
    change ((νS : Measure (ResetPath k)).map e.symm).map F = _
    rw [Measure.map_map Fmeas e.symm.measurable]
    have he : F ∘ e.symm = Subtype.val := by funext x; simp [F]
    rw [he, νS_map]
  clear_value ρ
  let Aflip (z : Bool × RelationPath k) : Bool × RelationPath k := (!z.1, z.2)
  have Aflip_measurable : Measurable Aflip :=
    ((measurable_of_countable Bool.not).comp measurable_fst).prodMk measurable_snd
  have Fflip : F ∘ Aflip = flipPath ∘ F := by
    funext z
    let y : ResetPath k := ⟨flipPath (F z), fun t => by
      have hq : kernel k (parryParameter k)
          (TwistedResetPaths.flip (F z t))
          (TwistedResetPaths.flip (F z (t + 1))) =
          kernel k (parryParameter k) (F z t) (F z (t + 1)) := by
        have hh := flip_kernel (F z t) (F z (t + 1))
        exact (ENNReal.ofReal_eq_ofReal_iff (hQ _ _) (hQ _ _)).mp hh
      rw [hq]
      exact (e z).property t⟩
    have hy : e.symm y = Aflip z := by
      apply Prod.ext
      · rw [(eread y).1]
        have h0 := (eread (e z)).1
        simpa [Aflip, y, flipPath, TwistedResetPaths.flip, F] using
          congrArg Bool.not h0.symm
      · apply Subtype.ext
        rw [(eread y).2]
        have hr := (eread (e z)).2
        have hrflip : readRelation (flipPath (F z)) = readRelation (F z) := by
          funext t
          simp [readRelation, flipPath, TwistedResetPaths.flip]
        change readRelation (flipPath (F z)) = z.2.val
        rw [hrflip]
        simpa [F] using hr.symm
    have he := congrArg (fun w => (e w).val) hy
    simpa [F, y] using he.symm
  have ρ_flip : (ρ : Measure (Bool × RelationPath k)).map Aflip = ρ := by
    apply Fembedding.map_injective
    rw [Measure.map_map Fmeas Aflip_measurable, Fflip,
      ← Measure.map_map flip_measurable Fmeas, ρ_map, ν_flip]
  let μ : ProbabilityMeasure (RelationPath k) := ρ.map measurable_snd.aemeasurable
  let u : Measure Bool := fairAnchor
  have : IsProbabilityMeasure u := inferInstanceAs (IsProbabilityMeasure (PMF.toMeasure _))
  have fair_singleton (A : Set (RelationPath k)) (hA : MeasurableSet A) (b : Bool) :
      (ρ : Measure (Bool × RelationPath k)) ({b} ×ˢ A) = (1 / 2 : ℝ≥0∞) * (μ : Measure _) A := by
    have he := congrArg (fun ζ : Measure (Bool × RelationPath k) => ζ ({false} ×ˢ A)) ρ_flip
    rw [Measure.map_apply Aflip_measurable ((measurableSet_singleton _).prod hA)] at he
    have hf : Aflip ⁻¹' ({false} ×ˢ A) = {true} ×ˢ A := by
      ext z
      cases h : z.1 <;> simp [Aflip, h]
    rw [hf] at he
    have hdis : Disjoint ({false} ×ˢ A) ({true} ×ˢ A) := by
      simp [Set.disjoint_left]
    have hun : ({false} ×ˢ A) ∪ ({true} ×ˢ A) = Prod.snd ⁻¹' A := by
      ext z
      cases h : z.1 <;> simp [h]
    have hsum : (ρ : Measure _) ({false} ×ˢ A) + (ρ : Measure _) ({true} ×ˢ A) =
        (μ : Measure _) A := by
      rw [← measure_union hdis ((measurableSet_singleton true).prod hA), hun]
      exact (Measure.map_apply measurable_snd hA).symm
    have hh : (ρ : Measure _) ({false} ×ˢ A) = (1 / 2 : ℝ≥0∞) * (μ : Measure _) A := by
      rw [← hsum, he, ← two_mul, ← mul_assoc]
      norm_num [ENNReal.inv_mul_cancel]
    cases b
    · exact hh
    · exact he.trans hh
  have product_law : u.prod (μ : Measure (RelationPath k)) = (ρ : Measure _) := by
    apply Measure.prod_eq
    intro S A hS hA
    have hs : S = ∅ ∨ S = {false} ∨ S = {true} ∨ S = Set.univ := by
      by_cases hf : false ∈ S <;> by_cases ht : true ∈ S
      · right; right; right; ext b; cases b <;> simp [hf, ht]
      · right; left; ext b; cases b <;> simp [hf, ht]
      · right; right; left; ext b; cases b <;> simp [hf, ht]
      · left; ext b; cases b <;> simp [hf, ht]
    rcases hs with rfl | rfl | rfl | rfl
    · simp
    · rw [fair_singleton _ hA]
      simp [u, fairAnchor]
    · rw [fair_singleton _ hA]
      simp [u, fairAnchor]
    · rw [measure_univ, one_mul]
      change (ρ : Measure (Bool × RelationPath k)) (Set.univ ×ˢ A) =
        ((ρ : Measure (Bool × RelationPath k)).map Prod.snd) A
      rw [Measure.map_apply measurable_snd hA]
      congr 1
      ext z
      simp
  have joint_law : (u.prod (μ : Measure (RelationPath k))).map F = ν := by
    rw [product_law, ρ_map]
  have suffix_independent (z : Bool × RelationPath k) (t : ℤ) :
      (F z t).2 = (F (false,z.2) t).2 := by
    apply Fin.ext
    have h1 := esuffix z t
    have h2 := esuffix (false,z.2) t
    dsimp only at h1 h2
    apply le_antisymm
    · by_contra h
      have he := h1.2 ((F (false,z.2) t).2.val) (by exact Nat.lt_of_not_ge h)
      rw [h2.1] at he
      contradiction
    · by_contra h
      have he := h2.2 ((F z t).2.val) (by exact Nat.lt_of_not_ge h)
      rw [h1.1] at he
      contradiction
  have μ_suffix_block (ell : ℤ) (n : ℕ) :
      (μ : Measure (RelationPath k)).map
        (fun r (i : Fin (n + 1)) => (F (false,r) (ell + i.val)).2) =
        ((pLaw n).map (fun w i => (w i).2)).toMeasure := by
    have hm : Measurable (fun r : RelationPath k => fun i : Fin (n + 1) =>
        (F (false,r) (ell + i.val)).2) := by
      apply measurable_pi_lambda
      intro i
      exact measurable_snd.comp ((measurable_pi_apply _).comp
        (Fmeas.comp (measurable_const.prodMk measurable_id)))
    change ((ρ : Measure (Bool × RelationPath k)).map Prod.snd).map _ = _
    rw [Measure.map_map hm measurable_snd]
    have he : (fun r (i : Fin (n + 1)) => (F (false,r) (ell + i.val)).2) ∘ Prod.snd =
        (fun w : Fin (n + 1) → State k => fun i => (w i).2) ∘
          ((fun x : ℤ → State k => fun i : Fin (n + 1) => x (ell + i.val)) ∘ F) := by
      funext z i
      exact (suffix_independent z (ell + i.val)).symm
    have hblock : Measurable
        (fun x : ℤ → State k => fun i : Fin (n + 1) => x (ell + i.val)) := by fun_prop
    rw [he, ← Measure.map_map (measurable_of_countable _) (hblock.comp Fmeas),
      ← Measure.map_map (by fun_prop) Fmeas, ρ_map, ν_block,
      PMF.toMeasure_map _ _ (measurable_of_countable _)]
  let shiftPath (x : ℤ → State k) : ℤ → State k := fun t => x (t + 1)
  have shift_measurable : Measurable shiftPath := by dsimp [shiftPath]; fun_prop
  have ν_shift : (ν : Measure (ℤ → State k)).map shiftPath = ν := by
    have hu := ν_unique (ν.map shift_measurable.aemeasurable) (fun l => by
      change ((ν : Measure (ℤ → State k)).map shiftPath).map _ = _
      rw [Measure.map_map (by fun_prop) shift_measurable]
      have he : (fun x (i : Fin (2 * l + 1)) => x ((i.val : ℤ) - l)) ∘ shiftPath =
          (fun x (i : Fin (2 * l + 1)) => x ((1 - (l : ℤ)) + i.val)) := by
        funext x i
        dsimp [shiftPath]
        congr 1
        omega
      rw [he, ν_block])
    exact congrArg ProbabilityMeasure.toMeasure hu
  let shiftAnchor (z : Bool × RelationPath k) : Bool × RelationPath k :=
    (xor z.1 (!z.2.val 0), relationShift z.2)
  have relation_shift_measurable : Measurable (@relationShift k) := by
    apply Measurable.subtype_mk
    exact measurable_pi_lambda _ fun t => (measurable_pi_apply (t + 1)).comp measurable_subtype_coe
  have anchor_shift_measurable : Measurable shiftAnchor := by
    apply Measurable.prodMk
    · have hp : Measurable (fun z : Bool × RelationPath k => (z.1, z.2.val 0)) :=
        measurable_fst.prodMk ((measurable_pi_apply 0).comp
          (measurable_subtype_coe.comp measurable_snd))
      exact (measurable_of_countable (fun p : Bool × Bool => xor p.1 (!p.2))).comp hp
    · exact relation_shift_measurable.comp measurable_snd
  have ρ_shift : (ρ : Measure (Bool × RelationPath k)).map shiftAnchor = ρ := by
    apply Fembedding.map_injective
    have he : F ∘ shiftAnchor = shiftPath ∘ F := funext eshift
    rw [Measure.map_map Fmeas anchor_shift_measurable, he,
      ← Measure.map_map shift_measurable Fmeas, ρ_map, ν_shift]
  have μ_shift : (μ : Measure (RelationPath k)).map relationShift = μ := by
    have he := congrArg (fun η : Measure (Bool × RelationPath k) => η.map Prod.snd) ρ_shift
    rw [Measure.map_map measurable_snd anchor_shift_measurable] at he
    change ((ρ : Measure (Bool × RelationPath k)).map Prod.snd).map relationShift = _
    rw [Measure.map_map relation_shift_measurable measurable_snd]
    exact he
  have signed_cylinder (ell : ℤ) (n : ℕ) (w : Fin (n + 1) → State k) :
      (ν : Measure (ℤ → State k)) {x | (fun i : Fin (n + 1) => x (ell + i.val)) = w} =
        ENNReal.ofReal (parryLaw k (w 0) * ∏ i : Fin n,
          kernel k (parryParameter k) (w i.castSucc) (w i.succ)) := by
    have he := congrArg (fun η : Measure (Fin (n + 1) → State k) => η {w}) (ν_block ell n)
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton w),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton w), pLaw_mass] at he
    calc
      _ = mass n w := he
      _ = _ := by
        dsimp [mass, π, Q]
        rw [ENNReal.ofReal_mul (hπ _), ENNReal.ofReal_prod_of_nonneg (fun i _ => hQ _ _)]
  have unsigned_cylinder (ell : ℤ) (n : ℕ) (v : Fin (n + 1) → Fin k) :
      (μ : Measure (RelationPath k))
        {r | (fun i : Fin (n + 1) => (F (false,r) (ell + i.val)).2) = v} =
        πu (v 0) * ∏ i : Fin n, U (v i.castSucc) (v i.succ) := by
    have hm : Measurable (fun r : RelationPath k => fun i : Fin (n + 1) =>
        (F (false,r) (ell + i.val)).2) := by
      exact measurable_pi_lambda _ fun i => measurable_snd.comp ((measurable_pi_apply _).comp
        (Fmeas.comp (measurable_const.prodMk measurable_id)))
    have he := congrArg (fun η : Measure (Fin (n + 1) → Fin k) => η {v}) (μ_suffix_block ell n)
    rw [Measure.map_apply hm (measurableSet_singleton v),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton v),
      unsigned_block_mass] at he
    exact he
  exact ⟨e, μ, ν, esign, esuffix, eread, eshift, μ_shift, ν_shift,
    joint_law, signed_cylinder, unsigned_cylinder⟩

end D5.S3.TotalVariation.ParryBilateralLaw
