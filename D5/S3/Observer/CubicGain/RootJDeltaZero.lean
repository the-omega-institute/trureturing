/- GID: D5/S3/Observer/CubicGain/RootJDeltaZero
   generality: G
   mirror-B: D5/B/S3/Observer/CubicGain/RootJDeltaZero
   mirror-E: none(waiver:whole-original-kernel-source-coupling)
   anchors: []
   utility: none
   digest: Original chronological reference rows retain the whole cubic coefficient kernel. -/

import D5.S3.Observer.Linear.GainRayNuisance
import D5.S3.Observer.Linear.GainRayWordGeometry

/-! The complete original reference matrix and its zero-inclusive cubic domain. -/

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.CubicGain.RootJDeltaZero
open D5.S3.Observer.Linear.GainRay

/-- Seven chronological binary digits, followed by the copy digit. J precedes M. -/
abbrev Slot := Fin 256
abbrev Blocks := Slot → Coeff 3

/-- Depth is stored minus one; a row lists every descendant after the first. -/
abbrev Row := (n : Fin 7) × Fin (2 ^ (n.val + 1)) × Fin (2 ^ (7 - n.val) - 1)

def prefixWord (n : ℕ) (p : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n => p / 2 ^ (n - 1 - i.val) % 2 == 0)

private theorem block_power (n : Fin 7) :
    2 ^ (n.val + 1) * 2 ^ (7 - n.val) = 256 := by
  fin_cases n <;> norm_num

private theorem reference_bound (n : Fin 7) (p : Fin (2 ^ (n.val + 1))) :
    p.val * 2 ^ (7 - n.val) < 256 := by
  have h := block_power n
  have hp := p.isLt
  have hz : 0 < 2 ^ (7 - n.val) := by positivity
  nlinarith

def reference (r : Row) : Slot :=
  ⟨r.2.1.val * 2 ^ (7 - r.1.val), reference_bound r.1 r.2.1⟩

def descendant (r : Row) : Slot :=
  ⟨r.2.1.val * 2 ^ (7 - r.1.val) + r.2.2.val + 1, by
    have hp := r.2.1.isLt
    have hq := r.2.2.isLt
    have hn := block_power r.1
    have hz : 0 < 2 ^ (7 - r.1.val) := by positivity
    have hq' : r.2.2.val + 1 < 2 ^ (7 - r.1.val) := by omega
    nlinarith⟩

/-- The last row of the native response matrix, with the normalized initial drift. -/
def normalized (w : List Bool) (P : Mat) : Coeff 3 →ₗ[ℝ] ℝ :=
  (LinearMap.proj ⟨w.length, by omega⟩).comp (responseMatrix 3 w P).mulVecLin -
    LinearMap.proj 0

/-- Exactly the nonreference rows of the original complete matrix. -/
def B (P : Slot → Mat) : Blocks →ₗ[ℝ] (Row → ℝ) where
  toFun x r := normalized (prefixWord (r.1.val + 1) r.2.1.val) (P (descendant r))
      (x (descendant r)) -
    normalized (prefixWord (r.1.val + 1) r.2.1.val) (P (reference r)) (x (reference r))
  map_add' x y := by ext r; simp; ring
  map_smul' a x := by ext r; simp; ring

abbrev V (P : Slot → Mat) := LinearMap.ker (B P)

/-- The full native coefficient block, including its freely varying constant. -/
def block (P : Slot → Mat) (q : Slot) : V P →ₗ[ℝ] Coeff 3 :=
  (LinearMap.proj q).comp (V P).subtype

def sample (P : Slot → Mat) (q : Slot) (i : ℕ) : V P →ₗ[ℝ] ℝ :=
  (LinearMap.proj (0 : Fin 1)).comp ((evaluate 3 1 (fun _ => (i : ℝ))).comp (block P q))

/-- H has the original four coefficients and identically zero constant coefficient. -/
def H (P : Slot → Mat) : V P →ₗ[ℝ] Coeff 3 :=
  block P 0 - (sample P 0 0).smulRight (Pi.single 0 1)

def history (P : Slot → Mat) (i : ℕ) : V P →ₗ[ℝ] ℝ :=
  (LinearMap.proj (0 : Fin 1)).comp ((evaluate 3 1 (fun _ => (i : ℝ))).comp (H P))

def E (P : Slot → Mat) : V P →ₗ[ℝ] ℝ := 3 • history P 4 - 2 • history P 2
def Delta (P : Slot → Mat) : V P →ₗ[ℝ] ℝ := history P 3 - history P 1
def F (P : Slot → Mat) : V P →ₗ[ℝ] ℝ := (1 / 2 : ℝ) •
  (history P 1 + history P 3) + E P

private theorem sample_eq (P : Slot → Mat) (q : Slot) (i : ℕ) (x : V P) :
    sample P q i x = (Linear.GainRay.gain 3 (x.val q)).eval (i : ℝ) := by
  exact evaluation_polynomial 3 1 (fun _ => (i : ℝ)) (x.val q) 0

private theorem sample_expand (P : Slot → Mat) (q : Slot) (i : ℕ) (x : V P) :
    sample P q i x = x.val q 0 + (i : ℝ) * x.val q 1 +
      (i : ℝ)^2 * x.val q 2 + (i : ℝ)^3 * x.val q 3 := by
  rw [sample_eq]
  simp [Linear.GainRay.gain, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ]
  ring

private theorem history_expand (P : Slot → Mat) (i : ℕ) (x : V P) :
    history P i x = (i : ℝ) * x.val 0 1 +
      (i : ℝ)^2 * x.val 0 2 + (i : ℝ)^3 * x.val 0 3 := by
  change evaluate 3 1 (fun _ => (i : ℝ)) (H P x) 0 = _
  rw [evaluation_polynomial]
  simp [Linear.GainRay.gain, Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_succ, H, sample_expand, block, Pi.single_apply]
  ring

private theorem delta_zero_history_coordinates (P : Slot → Mat) (delta : Delta P = 0) (x : V P) :
    F P x = 5 * x.val 0 2 + 60 * x.val 0 3 ∧
    E P x = 8 * x.val 0 2 + 72 * x.val 0 3 ∧
    history P 5 x = F P x ∧
    history P 6 x = 2 * F P x + E P x / 4 ∧
    history P 7 x = 21 / 5 * F P x := by
  have hd := congrArg (fun f : V P →ₗ[ℝ] ℝ => f x) delta
  simp only [Delta, LinearMap.sub_apply, LinearMap.zero_apply, history_expand] at hd
  simp only [F, E, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, history_expand]
  norm_num at hd ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private def t (P : Slot → Mat) (q : Slot) : ℝ := P q 0 1 + P q 1 0
private def d (P : Slot → Mat) (q : Slot) : ℝ := P q 1 1
private def c (P : Slot → Mat) (q : Slot) : ℝ := P q 1 0
private def s (P : Slot → Mat) (q : Slot) : ℝ := t P q + d P q

private theorem trace_one (P : Mat) (hP : LegalSource P) :
    P 0 0 + P 1 1 = 1 := by
  simpa [Matrix.trace, Fin.sum_univ_two] using hP.2.2

private theorem normalized_eval (w : List Bool) (P : Mat) (b : Coeff 3) :
    normalized w P b = Matrix.trace (acquisition w * P) *
      (b 0 + (w.length : ℝ) * b 1 + (w.length : ℝ)^2 * b 2 +
        (w.length : ℝ)^3 * b 3) - b 0 := by
  simp [normalized, responseMatrix, Matrix.mulVecLin_apply, Matrix.mulVec,
    dotProduct, Fin.sum_univ_succ, List.take_length]
  ring

private theorem prefix_response (P : Slot → Mat) (x : V P)
    (n : Fin 7) (p : Fin (2 ^ (n.val + 1))) (q : Slot)
    (hlo : p.val * 2 ^ (7 - n.val) ≤ q.val)
    (hhi : q.val < (p.val + 1) * 2 ^ (7 - n.val)) :
    normalized (prefixWord (n.val + 1) p.val) (P q) (x.val q) =
      normalized (prefixWord (n.val + 1) p.val)
        (P ⟨p.val * 2 ^ (7 - n.val), reference_bound n p⟩)
        (x.val ⟨p.val * 2 ^ (7 - n.val), reference_bound n p⟩) := by
  by_cases he : q.val = p.val * 2 ^ (7 - n.val)
  · have hq : q = ⟨p.val * 2 ^ (7 - n.val), reference_bound n p⟩ := Fin.ext he
    rw [hq]
  · let r : Row := ⟨n, p, ⟨q.val - p.val * 2 ^ (7 - n.val) - 1, by
      have hz : 0 < 2 ^ (7 - n.val) := by positivity
      have hh : q.val < p.val * 2 ^ (7 - n.val) + 2 ^ (7 - n.val) := by
        simpa [add_mul] using hhi
      omega⟩⟩
    have hr : descendant r = q := by
      apply Fin.ext
      dsimp [descendant, r]
      omega
    have hb := congrFun x.property r
    change normalized _ (P (descendant r)) (x.val (descendant r)) -
      normalized _ (P (reference r)) (x.val (reference r)) = 0 at hb
    rw [hr] at hb
    exact sub_eq_zero.mp hb

private theorem j4_ancestors (P : Slot → Mat) (x : V P) (q : Slot) (hq : q.val < 16)
    (n : Fin 4) :
    normalized (prefixWord (n.val + 1) 0) (P q) (x.val q) =
      normalized (prefixWord (n.val + 1) 0) (P 0) (x.val 0) := by
  have hh := prefix_response P x ⟨n.val, by omega⟩ 0 q (by simp)
    (by fin_cases n <;> norm_num <;> omega)
  have hz : (⟨(0 : Fin (2 ^ (n.val + 1))).val * 2 ^ (7 - n.val),
      reference_bound ⟨n.val, by omega⟩ 0⟩ : Slot) = 0 := by
    apply Fin.ext
    simp
  rw [hz] at hh
  exact hh

private theorem j4_propagation (P : Slot → Mat) (legal : ∀ q, LegalSource (P q))
    (unit : t P 0 = 1) (delta : Delta P = 0) (q : Slot) (hq : q.val < 16) (x : V P) :
    (∀ i : Fin 3, x.val q i.succ = x.val 0 i.succ) ∧
      (t P q - 1) * (x.val q 0 + F P x - E P x) = 0 := by
  have h1 := j4_ancestors P x q hq 0
  have h2 := j4_ancestors P x q hq 1
  have h3 := j4_ancestors P x q hq 2
  have h4 := j4_ancestors P x q hq 3
  have ht := trace_one (P q) (legal q)
  have ht0 := trace_one (P 0) (legal 0)
  have hd := congrArg (fun f : V P →ₗ[ℝ] ℝ => f x) delta
  simp only [Delta, LinearMap.sub_apply, LinearMap.zero_apply, history_expand] at hd
  norm_num at hd
  have hu : P 0 0 1 + P 0 1 0 = 1 := unit
  have hu' : P 0 1 0 + P 0 0 1 = 1 := by linarith
  simp only [normalized_eval] at h1 h2 h3 h4
  norm_num [prefixWord, List.ofFn_succ, acquisition, Raw,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, ht, ht0, hu'] at h1 h2 h3 h4
  have htq : t P q ≠ 0 := ne_of_gt (add_pos ((legal q).1 0 1) ((legal q).1 1 0))
  have hodd : 2 * x.val q 1 + 8 * x.val q 2 + 26 * x.val q 3 = 0 := by
    apply (mul_eq_zero.mp (show t P q *
      (2 * x.val q 1 + 8 * x.val q 2 + 26 * x.val q 3) = 0 by
        dsimp [t]; nlinarith [h1, h3])).resolve_left htq
  have hn1 : x.val q 1 = x.val 0 1 := by linarith
  have hn2 : x.val q 2 = x.val 0 2 := by linarith
  have hn3 : x.val q 3 = x.val 0 3 := by linarith
  refine ⟨?_, ?_⟩
  · intro i
    fin_cases i <;> assumption
  · have hA : F P x - E P x = x.val 0 1 + x.val 0 2 + x.val 0 3 := by
      simp only [F, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, history_expand]
      norm_num only [Nat.cast_ofNat]
      linarith
    rw [show x.val q 0 + F P x - E P x = x.val q 0 + (F P x - E P x) by ring, hA]
    dsimp [t]
    rw [hn1, hn2, hn3] at h1
    nlinarith [h1]

private theorem history_coefficients (P : Slot → Mat) (delta : Delta P = 0) (x : V P) :
    H P x = F P x • ![0, 23/15, -3/5, 1/15] +
      E P x • ![0, -35/24, 1/2, -1/24] := by
  have h := delta_zero_history_coordinates P delta x
  have hd := congrArg (fun f : V P →ₗ[ℝ] ℝ => f x) delta
  simp only [Delta, LinearMap.sub_apply, LinearMap.zero_apply, history_expand] at hd
  norm_num at hd
  ext i
  fin_cases i
  · simp [H, block, sample_expand, Pi.single_apply]
  all_goals
    simp [H, block, Pi.single_apply]
    linarith [h.1, h.2.1]

private theorem independent_history_forms (P : Slot → Mat) (delta : Delta P = 0)
    (rankH : Module.finrank ℝ (LinearMap.range (H P)) = 2) (nonzeroE : E P ≠ 0) :
    ∀ a b : ℝ, (∀ x : V P, a * F P x + b * E P x = 0) → a = 0 ∧ b = 0 := by
  intro a b hab
  have ha : a = 0 := by
    by_contra hna
    let v : Coeff 3 := (-b / a) • ![0, 23/15, -3/5, 1/15] + ![0, -35/24, 1/2, -1/24]
    have hF (x : V P) : F P x = (-b / a) * E P x := by
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hna).mpr
      have hh := hab x
      nlinarith
    have hle : LinearMap.range (H P) ≤ Submodule.span ℝ ({v} : Set (Coeff 3)) := by
      rintro _ ⟨x, rfl⟩
      rw [history_coefficients P delta x, hF]
      have he : ((-b / a) * E P x) • ![0, 23/15, -3/5, 1/15] +
          E P x • ![0, -35/24, 1/2, -1/24] = E P x • v := by
        dsimp [v]
        module
      rw [he]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    have hs : Module.finrank ℝ (Submodule.span ℝ ({v} : Set (Coeff 3))) ≤ 1 := by
      simpa using finrank_span_le_card (R := ℝ) ({v} : Set (Coeff 3))
    have hh := (Submodule.finrank_mono hle).trans hs
    omega
  refine ⟨ha, ?_⟩
  by_contra hb
  apply nonzeroE
  ext x
  have hh := hab x
  simp only [ha, zero_mul, zero_add] at hh
  exact (mul_eq_zero.mp hh).resolve_left hb

private theorem normalized_j4 (P : Slot → Mat) (legal : ∀ q, LegalSource (P q))
    (unit : t P 0 = 1) (delta : Delta P = 0) (q : Slot) (hq : q.val < 16)
    (w : List Bool) (x : V P) :
    normalized w (P q) (x.val q) = Matrix.trace (acquisition w * P q) *
      (x.val q 0 + history P w.length x) - x.val q 0 := by
  have hh := (j4_propagation P legal unit delta q hq x).1
  have h1 := hh 0
  have h2 := hh 1
  have h3 := hh 2
  simp only [Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Fin.reduceSucc] at h1 h2 h3
  rw [normalized_eval, history_expand, h1, h2, h3]
  ring

private theorem native_fifth (P : Slot → Mat) (legal : ∀ q, LegalSource (P q))
    (unit : t P 0 = 1) (delta : Delta P = 0) (q : Slot) (hlo : 8 ≤ q.val)
    (hhi : q.val < 16) (x : V P) :
    (s P q - 1) * x.val q 0 + s P q * F P x =
      (s P 8 - 1) * x.val 8 0 + s P 8 * F P x := by
  have hh := prefix_response P x 4 1 q (by norm_num; exact hlo) (by norm_num; exact hhi)
  change normalized (prefixWord 5 1) (P q) (x.val q) =
    normalized (prefixWord 5 1) (P 8) (x.val 8) at hh
  rw [normalized_j4 P legal unit delta q hhi,
    normalized_j4 P legal unit delta 8 (by decide)] at hh
  have hc := delta_zero_history_coordinates P delta x
  norm_num [prefixWord, List.ofFn_succ, acquisition, Raw,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] at hh
  rw [hc.2.2.1] at hh
  dsimp [s, t, d]
  nlinarith [hh]

private theorem native_sixth_j (P : Slot → Mat) (legal : ∀ q, LegalSource (P q))
    (unit : t P 0 = 1) (delta : Delta P = 0) (q : Slot) (hlo : 8 ≤ q.val)
    (hhi : q.val < 12) (x : V P) :
    c P q * x.val q 0 + (1 + c P q) * (2 * F P x + E P x / 4) =
      c P 8 * x.val 8 0 + (1 + c P 8) * (2 * F P x + E P x / 4) := by
  have hh := prefix_response P x 5 2 q (by norm_num; exact hlo) (by norm_num; exact hhi)
  change normalized (prefixWord 6 2) (P q) (x.val q) =
    normalized (prefixWord 6 2) (P 8) (x.val 8) at hh
  rw [normalized_j4 P legal unit delta q (by omega),
    normalized_j4 P legal unit delta 8 (by decide)] at hh
  have ht := trace_one (P q) (legal q)
  have ht8 := trace_one (P 8) (legal 8)
  have hc := delta_zero_history_coordinates P delta x
  norm_num [prefixWord, List.ofFn_succ, acquisition, Raw,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] at hh
  rw [hc.2.2.2.1] at hh
  have htr : P q 0 0 + (P q 1 0 + P q 1 1) = 1 + c P q := by dsimp [c]; linarith
  have htr8 : P 8 0 0 + (P 8 1 0 + P 8 1 1) = 1 + c P 8 := by dsimp [c]; linarith
  rw [htr, htr8] at hh
  nlinarith [hh]

private theorem native_sixth_m (P : Slot → Mat) (legal : ∀ q, LegalSource (P q))
    (unit : t P 0 = 1) (delta : Delta P = 0) (q : Slot) (hlo : 12 ≤ q.val)
    (hhi : q.val < 16) (x : V P) :
    s P q * x.val q 0 + (1 + s P q) * (2 * F P x + E P x / 4) =
      s P 12 * x.val 12 0 + (1 + s P 12) * (2 * F P x + E P x / 4) := by
  have hh := prefix_response P x 5 3 q (by norm_num; exact hlo) (by norm_num; exact hhi)
  change normalized (prefixWord 6 3) (P q) (x.val q) =
    normalized (prefixWord 6 3) (P 12) (x.val 12) at hh
  rw [normalized_j4 P legal unit delta q hhi,
    normalized_j4 P legal unit delta 12 (by decide)] at hh
  have ht := trace_one (P q) (legal q)
  have ht12 := trace_one (P 12) (legal 12)
  have hc := delta_zero_history_coordinates P delta x
  norm_num [prefixWord, List.ofFn_succ, acquisition, Raw,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] at hh
  rw [hc.2.2.2.1] at hh
  dsimp [s, t, d]
  nlinarith [hh]

private theorem fixed_leaf_algebra {X : Type} (f e : X → ℝ)
    (k : Slot → X → ℝ) (t d c s : Slot → ℝ)
    (hs : ∀ q, s q = t q + d q) (hd : ∀ q, 0 < d q) (hc : ∀ q, 0 < c q)
    (indep : ∀ a b : ℝ, (∀ x, a * f x + b * e x = 0) → a = 0 ∧ b = 0)
    (ancestor : ∀ q, q.val < 16 → ∀ x, (t q - 1) * (k q x + f x - e x) = 0)
    (fifth : ∀ q, 8 ≤ q.val → q.val < 16 → ∀ x,
      (s q - 1) * k q x + s q * f x = (s 8 - 1) * k 8 x + s 8 * f x)
    (sixthJ : ∀ q, 8 ≤ q.val → q.val < 12 → ∀ x,
      c q * k q x + (1 + c q) * (2 * f x + e x / 4) =
      c 8 * k 8 x + (1 + c 8) * (2 * f x + e x / 4))
    (sixthM : ∀ q, 12 ≤ q.val → q.val < 16 → ∀ x,
      s q * k q x + (1 + s q) * (2 * f x + e x / 4) =
      s 12 * k 12 x + (1 + s 12) * (2 * f x + e x / 4))
    (seventhA : ∀ x, (s 9 - 1) * k 9 x + s 9 * (21/5 * f x) =
      (s 8 - 1) * k 8 x + s 8 * (21/5 * f x))
    (seventhB : ∀ x, (t 13 + c 13) * k 13 x + (1 + t 13 + c 13) * (21/5 * f x) =
      (t 12 + c 12) * k 12 x + (1 + t 12 + c 12) * (21/5 * f x))
    (seventhC : ∀ x, (s 11 + d 11 - 1) * k 11 x + (s 11 + d 11) * (21/5 * f x) =
      (s 10 + d 10 - 1) * k 10 x + (s 10 + d 10) * (21/5 * f x)) :
    ∃ q : Slot, (q = 8 ∨ q = 12 ∨ q = 10) ∧
      ∃ r : Slot, r.val = q.val + 1 ∧ s q = s r ∧ d q = d r ∧ c q = c r ∧
        ∀ x, k q x = k r x := by
  have sn : s 8 = s 9 := by
    have hh := (indep (s 8 - s 9) 0 (fun x => by
      have h5 := fifth 9 (by decide) (by decide) x
      have h7 := seventhA x
      nlinarith)).1
    linarith
  have const_nonunit (q : Slot) (hq : q.val < 16) (hu : t q ≠ 1) (x : X) :
      k q x = e x - f x := by
    have hh := (mul_eq_zero.mp (ancestor q hq x)).resolve_left (sub_ne_zero.mpr hu)
    linarith
  have same_k : ∀ x, k 8 x = k 9 x := by
    by_cases hu8 : t 8 = 1
    · have hz : s 8 - 1 ≠ 0 := by have hh := hs 8; have hp := hd 8; rw [hu8] at hh; linarith
      intro x
      have hh : (s 8 - 1) * (k 8 x - k 9 x) = 0 := by
        have h := fifth 9 (by decide) (by decide) x
        rw [← sn] at h
        nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hz)
    · by_cases hu9 : t 9 = 1
      · have hz : s 8 - 1 ≠ 0 := by have hh := hs 9; have hp := hd 9; rw [hu9, ← sn] at hh; linarith
        intro x
        have hh : (s 8 - 1) * (k 8 x - k 9 x) = 0 := by
          have h := fifth 9 (by decide) (by decide) x
          rw [← sn] at h
          nlinarith
        exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left hz)
      · intro x
        rw [const_nonunit 8 (by decide) hu8 x, const_nonunit 9 (by decide) hu9 x]
  by_cases closeA : d 8 = d 9 ∧ c 8 = c 9
  · exact ⟨8, Or.inl rfl, 9, rfl, sn, closeA.1, closeA.2, same_k⟩
  by_cases units : t 8 = 1 ∧ t 9 = 1
  · have dn : d 8 = d 9 := by have h8 := hs 8; have h9 := hs 9; rw [units.1] at h8; rw [units.2] at h9; linarith
    have cn : c 8 ≠ c 9 := fun he => closeA ⟨dn, he⟩
    have k8 (x : X) : k 8 x = -(2 * f x + e x / 4) := by
      have hh : (c 8 - c 9) * (k 8 x + (2 * f x + e x / 4)) = 0 := by
        have h := sixthJ 9 (by decide) (by decide) x
        rw [← same_k x] at h
        nlinarith
      have hz := (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr cn)
      linarith
    have all_unit (q : Slot) (hlo : 8 ≤ q.val) (hhi : q.val < 16) : t q = 1 := by
      by_contra hu
      have he := (indep (d 8) ((s q - 1) + d 8 / 4) (fun x => by
        have h5 := fifth q hlo hhi x
        rw [const_nonunit q hhi hu x, k8 x] at h5
        have h8 := hs 8
        rw [units.1] at h8
        nlinarith)).1
      have hp := hd 8
      linarith
    have u12 := all_unit 12 (by decide) (by decide)
    have u13 := all_unit 13 (by decide) (by decide)
    have kr (q : Slot) (hlo : 8 ≤ q.val) (hhi : q.val < 16) (x : X) :
        d q * (k q x + f x) + d 8 * (f x + e x / 4) = 0 := by
      have h5 := fifth q hlo hhi x
      rw [k8 x] at h5
      have hq := hs q
      rw [all_unit q hlo hhi] at hq
      have h8 := hs 8
      rw [units.1] at h8
      nlinarith
    have km (x : X) : (k 12 x - k 13 x) + (d 12 - d 13) * (f x + e x / 4) = 0 := by
      have hm := sixthM 13 (by decide) (by decide) x
      have h5a := fifth 12 (by decide) (by decide) x
      have h5b := fifth 13 (by decide) (by decide) x
      have h12 := hs 12
      have h13 := hs 13
      rw [u12] at h12
      rw [u13] at h13
      nlinarith
    have dd : d 12 = d 13 := by
      have hzero := (indep ((d 12 - d 13) * (d 12 * d 13 + d 8))
        ((d 12 - d 13) * (d 12 * d 13 + d 8) / 4) (fun x => by
          have h12 := kr 12 (by decide) (by decide) x
          have h13 := kr 13 (by decide) (by decide) x
          have hm := km x
          linear_combination d 12 * d 13 * hm - d 13 * h12 + d 12 * h13)).1
      have hp : 0 < d 12 * d 13 + d 8 := by positivity
      have hn := (mul_eq_zero.mp hzero).resolve_right (ne_of_gt hp)
      exact sub_eq_zero.mp hn
    have kk (x : X) : k 12 x = k 13 x := by
      have h12 := kr 12 (by decide) (by decide) x
      have h13 := kr 13 (by decide) (by decide) x
      rw [← dd] at h13
      have hh : d 12 * (k 12 x - k 13 x) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (ne_of_gt (hd 12)))
    have cc : c 12 = c 13 := by
      by_contra he
      have kg (x : X) : k 12 x + (21/5 * f x) = 0 := by
        have hh : (c 12 - c 13) * (k 12 x + (21/5 * f x)) = 0 := by
          have h := seventhB x
          rw [u12, u13, ← kk x] at h
          nlinarith
        exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr he)
      have hz := (indep (16/5 * d 12 - d 8) (-d 8 / 4) (fun x => by
        have h := kr 12 (by decide) (by decide) x
        have hh := kg x
        linear_combination d 12 * hh - h)).2
      have hp := hd 8
      linarith
    refine ⟨12, Or.inr (Or.inl rfl), 13, rfl, ?_, dd, cc, kk⟩
    rw [hs 12, hs 13, u12, u13, dd]
  · have base (x : X) : k 8 x = e x - f x := by
      by_cases hu8 : t 8 = 1
      · have hu9 : t 9 ≠ 1 := fun he => units ⟨hu8, he⟩
        rw [same_k x]
        exact const_nonunit 9 (by decide) hu9 x
      · exact const_nonunit 8 (by decide) hu8 x
    have branch (q : Slot) (hlo : 8 ≤ q.val) (hhi : q.val < 12) :
        s q = s 8 ∧ c q = c 8 ∧ ∀ x, k q x = e x - f x := by
      by_cases hu : t q = 1
      · have h5 (x : X) : d q * (k q x + f x) = (s 8 - 1) * e x := by
          have h := fifth q hlo (by omega) x
          rw [base x] at h
          have hq := hs q
          rw [hu] at hq
          nlinarith
        have h6 (x : X) : c q * (k q x + (2 * f x + e x / 4)) =
            c 8 * (f x + 5/4 * e x) := by
          have h := sixthJ q hlo hhi x
          rw [base x] at h
          nlinarith
        have coeffs := indep (d q * (c q - c 8))
          (c q * (s 8 - 1 + d q / 4) - 5/4 * d q * c 8) (fun x => by
            have h := h5 x
            have hh := h6 x
            linear_combination d q * hh - c q * h)
        have ceq : c q = c 8 := sub_eq_zero.mp
          ((mul_eq_zero.mp coeffs.1).resolve_left (ne_of_gt (hd q)))
        have deq : d q = s 8 - 1 := by
          have hz : c q * (s 8 - 1 - d q) = 0 := by
            rw [← ceq] at coeffs
            nlinarith [coeffs.2]
          have hh := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hc q))
          linarith
        refine ⟨by rw [hs q, hu, deq]; ring, ceq, ?_⟩
        intro x
        have hh : d q * (k q x + f x - e x) = 0 := by
          have h := h5 x
          rw [← deq] at h
          nlinarith
        have hz := (mul_eq_zero.mp hh).resolve_left (ne_of_gt (hd q))
        linarith
      · have kq := const_nonunit q (by omega) hu
        have se : s q = s 8 := by
          have hh := (indep 0 (s q - s 8) (fun x => by
            have h := fifth q hlo (by omega) x
            rw [kq x, base x] at h
            nlinarith)).2
          linarith
        have ce : c q = c 8 := by
          have hh := (indep (c q - c 8) (5/4 * (c q - c 8)) (fun x => by
            have h := sixthJ q hlo hhi x
            rw [kq x, base x] at h
            nlinarith)).1
          linarith
        exact ⟨se, ce, kq⟩
    have h10 := branch 10 (by decide) (by decide)
    have h11 := branch 11 (by decide) (by decide)
    have deq : d 10 = d 11 := by
      have hh := (indep (16/5 * (d 10 - d 11)) (d 10 - d 11) (fun x => by
        have h := seventhC x
        rw [h10.2.2 x, h11.2.2 x, h10.1, h11.1] at h
        nlinarith)).2
      linarith
    exact ⟨10, Or.inr (Or.inr rfl), 11, rfl, h10.1.trans h11.1.symm, deq,
      h10.2.1.trans h11.2.1.symm, fun x => (h10.2.2 x).trans (h11.2.2 x).symm⟩

private theorem native_seventh (P : Slot → Mat) (legal : ∀ q, LegalSource (P q))
    (unit : t P 0 = 1) (delta : Delta P = 0) (x : V P) :
    ((s P 9 - 1) * x.val 9 0 + s P 9 * (21/5 * F P x) =
      (s P 8 - 1) * x.val 8 0 + s P 8 * (21/5 * F P x)) ∧
    ((t P 13 + c P 13) * x.val 13 0 + (1 + t P 13 + c P 13) * (21/5 * F P x) =
      (t P 12 + c P 12) * x.val 12 0 + (1 + t P 12 + c P 12) * (21/5 * F P x)) ∧
    ((s P 11 + d P 11 - 1) * x.val 11 0 + (s P 11 + d P 11) * (21/5 * F P x) =
      (s P 10 + d P 10 - 1) * x.val 10 0 + (s P 10 + d P 10) * (21/5 * F P x)) := by
  have ha := prefix_response P x 6 4 9 (by norm_num) (by norm_num)
  have hb := prefix_response P x 6 6 13 (by norm_num) (by norm_num)
  have hc := prefix_response P x 6 5 11 (by norm_num) (by norm_num)
  change normalized (prefixWord 7 4) (P 9) (x.val 9) =
    normalized (prefixWord 7 4) (P 8) (x.val 8) at ha
  change normalized (prefixWord 7 6) (P 13) (x.val 13) =
    normalized (prefixWord 7 6) (P 12) (x.val 12) at hb
  change normalized (prefixWord 7 5) (P 11) (x.val 11) =
    normalized (prefixWord 7 5) (P 10) (x.val 10) at hc
  rw [normalized_j4 P legal unit delta 9 (by decide),
    normalized_j4 P legal unit delta 8 (by decide)] at ha
  rw [normalized_j4 P legal unit delta 13 (by decide),
    normalized_j4 P legal unit delta 12 (by decide)] at hb
  rw [normalized_j4 P legal unit delta 11 (by decide),
    normalized_j4 P legal unit delta 10 (by decide)] at hc
  have ht12 := trace_one (P 12) (legal 12)
  have ht13 := trace_one (P 13) (legal 13)
  have hp := (delta_zero_history_coordinates P delta x).2.2.2.2
  norm_num [prefixWord, List.ofFn_succ, acquisition, Raw,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
    D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
    Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two] at ha hb hc
  rw [hp] at ha hb hc
  dsimp [s, t, c, d]
  refine ⟨by nlinarith [ha], by nlinarith [hb], by nlinarith [hc]⟩

/-- One original fixed leaf, with the equality of the entire coefficient block on V. -/
theorem fixed_original_leaf (P : Slot → Mat) (legal : ∀ q, LegalSource (P q))
    (unit0 : P 0 0 1 + P 0 1 0 = 1) (unit1 : P 1 0 1 + P 1 1 0 = 1)
    (rankH : Module.finrank ℝ (LinearMap.range (H P)) = 2)
    (nonzeroE : E P ≠ 0) (delta : Delta P = 0) :
    (P 8 = P 9 ∧ ∀ x : V P, x.val 8 = x.val 9) ∨
    (P 12 = P 13 ∧ ∀ x : V P, x.val 12 = x.val 13) ∨
    (P 10 = P 11 ∧ ∀ x : V P, x.val 10 = x.val 11) := by
  have unit : t P 0 = 1 := unit0
  have alg := fixed_leaf_algebra (fun x : V P => F P x) (fun x => E P x)
    (fun q x => x.val q 0) (t P) (d P) (c P) (s P)
    (fun _ => rfl) (fun q => (legal q).1 1 1) (fun q => (legal q).1 1 0)
    (independent_history_forms P delta rankH nonzeroE)
    (fun q hq x => (j4_propagation P legal unit delta q hq x).2)
    (native_fifth P legal unit delta)
    (native_sixth_j P legal unit delta)
    (native_sixth_m P legal unit delta)
    (fun x => (native_seventh P legal unit delta x).1)
    (fun x => (native_seventh P legal unit delta x).2.1)
    (fun x => (native_seventh P legal unit delta x).2.2)
  obtain ⟨q, hq, r, hr, hsq, hdq, hcq, hkq⟩ := alg
  have qsmall : q.val < 16 := by rcases hq with rfl | rfl | rfl <;> decide
  have rsmall : r.val < 16 := by rcases hq with rfl | rfl | rfl <;> norm_num at hr ⊢ <;> omega
  have src : P q = P r := by
    have hqt := trace_one (P q) (legal q)
    have hrt := trace_one (P r) (legal r)
    dsimp [s, t, c, d] at hsq hdq hcq
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp <;> linarith
  have coeffs (x : V P) : x.val q = x.val r := by
    have hqj := (j4_propagation P legal unit delta q qsmall x).1
    have hrj := (j4_propagation P legal unit delta r rsmall x).1
    ext i
    fin_cases i
    · exact hkq x
    · exact (hqj 0).trans (hrj 0).symm
    · exact (hqj 1).trans (hrj 1).symm
    · exact (hqj 2).trans (hrj 2).symm
  rcases hq with rfl | rfl | rfl
  · have he : r = 9 := Fin.ext (by norm_num at hr; omega)
    subst r
    exact Or.inl ⟨src, coeffs⟩
  · have he : r = 13 := Fin.ext (by norm_num at hr; omega)
    subst r
    exact Or.inr (Or.inl ⟨src, coeffs⟩)
  · have he : r = 11 := Fin.ext (by norm_num at hr; omega)
    subst r
    exact Or.inr (Or.inr ⟨src, coeffs⟩)

end D5.S3.Observer.CubicGain.RootJDeltaZero
