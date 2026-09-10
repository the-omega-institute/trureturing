/- GID: D5/S1/Recurrence/Residue/QuarticEGFFixedPoint
   generality: G
   mirror-B: D5/B/S1/Recurrence/Residue/QuarticEGFFixedPoint
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Natural coefficients and the unique rational formal solution of the A396804 equation. -/

import D5.S1.Recurrence.Residue.IntegralEGFComposition

open PowerSeries Finset
open D5.S1.Recurrence.Residue.IntegralEGFComposition

namespace D5.S1.Recurrence.Residue.QuarticEGFFixedPoint

noncomputable def encode (s : ℕ → ℚ) : PowerSeries ℚ := mk (fun n => s n / n.factorial)

@[simp] theorem eCoeff_encode (s : ℕ → ℚ) (n : ℕ) : eCoeff (encode s) n = s n := by
  simp only [encode, eCoeff, coeff_mk]
  exact mul_div_cancel₀ _ (by exact_mod_cast n.factorial_ne_zero)

theorem eCoeff_ext {f g : PowerSeries ℚ} (h : ∀ n, eCoeff f n = eCoeff g n) : f = g := by
  ext n
  exact mul_left_cancel₀ (by exact_mod_cast n.factorial_ne_zero) (h n)

@[simp] theorem constantCoeff_encode (s : ℕ → ℚ) : constantCoeff (encode s) = s 0 := by
  rw [← eCoeff_zero, eCoeff_encode]

theorem encode_composition (f g : ℕ → ℚ) (hg : g 0 = 0) :
    encode (composition f g) = (encode f).subst (encode g) := by
  apply eCoeff_ext
  intro n
  rw [eCoeff_encode, eCoeff_composition _ _ (by simp [hg])]
  simp only [show eCoeff (encode f) = f from funext (eCoeff_encode f),
    show eCoeff (encode g) = g from funext (eCoeff_encode g)]

def identity {R : Type*} [Zero R] [One R] (n : ℕ) : R := if n = 1 then 1 else 0

def iterate {R : Type*} [CommSemiring R] (f : ℕ → R) : ℕ → ℕ → R
  | 0 => identity
  | k + 1 => composition f (iterate f k)

theorem iterate_congr {R : Type*} [CommSemiring R] {f g : ℕ → R} {n : ℕ}
    (h : ∀ i ≤ n, f i = g i) (k : ℕ) : iterate f k n = iterate g k n := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    apply composition_congr h
    intro i hi
    exact ih (fun j hj => h j (hj.trans hi))

theorem iterate_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (f : ℕ → R) (k n : ℕ) :
    φ (iterate f k n) = iterate (fun j => φ (f j)) k n := by
  induction k generalizing n with
  | zero => simp [iterate, identity]
  | succ k ih =>
    rw [iterate, composition_map, iterate]
    congr 1
    funext j
    exact ih j

noncomputable def iterateComp (f : PowerSeries ℚ) : ℕ → PowerSeries ℚ
  | 0 => X
  | k + 1 => f.subst (iterateComp f k)

@[simp] theorem iterateComp_zero_coeff {f : PowerSeries ℚ}
    (hf : constantCoeff f = 0) (k : ℕ) : constantCoeff (iterateComp f k) = 0 := by
  induction k with
  | zero => simp [iterateComp]
  | succ k ih => exact constantCoeff_subst_eq_zero ih f hf

theorem eCoeff_iterate {f : PowerSeries ℚ} (hf : constantCoeff f = 0) (k : ℕ) :
    eCoeff (iterateComp f k) = iterate (eCoeff f) k := by
  induction k with
  | zero => funext n; simp [iterateComp, iterate, identity]
  | succ k ih =>
    funext n
    rw [iterateComp, eCoeff_composition _ _ (iterateComp_zero_coeff hf k), ih]
    rfl

def step {R : Type*} [CommSemiring R] (f : ℕ → R) : ℕ → R
  | 0 => 0
  | n + 1 => (n + 1 : R) * composition (fun _ => 1) (iterate f 4) n

theorem step_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (f : ℕ → R) (n : ℕ) :
    φ (step f n) = step (fun j => φ (f j)) n := by
  cases n with
  | zero => simp [step]
  | succ n =>
    simp only [step, map_mul, map_add, map_natCast, map_one, composition_map]
    congr 2
    funext j
    exact iterate_map φ f 4 j

theorem step_contract {R : Type*} [CommSemiring R] {f g : ℕ → R} {d : ℕ}
    (h : ∀ i < d, f i = g i) : ∀ i < d + 1, step f i = step g i := by
  intro i hi
  cases i with
  | zero => rfl
  | succ i =>
    simp only [step]
    congr 1
    apply composition_congr (fun _ _ => rfl)
    intro j hj
    exact iterate_congr (fun k hk => h k (by omega)) 4

theorem step_coeff {f : PowerSeries ℚ} (hf : constantCoeff f = 0) :
    eCoeff (X * (exp ℚ).subst (iterateComp f 4)) = step (eCoeff f) := by
  funext n
  cases n with
  | zero => simp [step]
  | succ n =>
    rw [eCoeff_X_mul, eCoeff_composition _ _ (iterateComp_zero_coeff hf 4),
      eCoeff_iterate hf]
    simp only [show eCoeff (exp ℚ) = (fun _ => 1) from funext eCoeff_exp, step]

def approximation : ℕ → ℕ → ℕ
  | 0 => fun n => n
  | d + 1 => step (approximation d)

theorem approximation_stable {d stage : ℕ} (h : d ≤ stage) :
    ∀ i < d, approximation d i = approximation stage i := by
  induction d generalizing stage with
  | zero => intro i hi; omega
  | succ d ih =>
    cases stage with
    | zero => omega
    | succ stage => exact step_contract (ih (by omega))

/-- The sequence is constructed in the natural numbers, without assuming integrality. -/
def a (n : ℕ) : ℕ := approximation (n + 1) n

theorem a_agrees (d : ℕ) : ∀ i < d, a i = approximation d i := by
  intro i hi
  exact approximation_stable (by omega : i + 1 ≤ d) i (by omega)

theorem a_fixed : a = step a := by
  funext n
  have h := step_contract (a_agrees (n + 1)) n (by omega)
  exact (a_agrees (n + 2) n (by omega)).trans h.symm

@[simp] theorem a_zero : a 0 = 0 := by rw [a_fixed]; rfl

noncomputable def A : PowerSeries ℚ := encode (fun n => a n)

/-- Independent natural integrality, with the exact factorial normalization. -/
theorem integral_coefficients (n : ℕ) : (a n : ℚ) = n.factorial * coeff n A := by
  simpa only [A, eCoeff] using (eCoeff_encode (fun j => (a j : ℚ)) n).symm

theorem A_equation : constantCoeff A = 0 ∧ A = X * (exp ℚ).subst (iterateComp A 4) := by
  have hz : constantCoeff A = 0 := by simp [A]
  refine ⟨hz, eCoeff_ext ?_⟩
  intro n
  rw [step_coeff hz]
  change eCoeff (encode _) n = _
  rw [eCoeff_encode, show eCoeff A = (fun n => (a n : ℚ)) from funext (eCoeff_encode _)]
  exact (congrArg (fun k : ℕ => (k : ℚ)) (congrFun a_fixed n)).trans
    (step_map (Nat.castRingHom ℚ) a n)

theorem fixed_unique {f g : PowerSeries ℚ} (hf : constantCoeff f = 0)
    (hg : constantCoeff g = 0)
    (ef : f = X * (exp ℚ).subst (iterateComp f 4))
    (eg : g = X * (exp ℚ).subst (iterateComp g 4)) : f = g := by
  have hf' : eCoeff f = step (eCoeff f) := (congrArg eCoeff ef).trans (step_coeff hf)
  have hg' : eCoeff g = step (eCoeff g) := (congrArg eCoeff eg).trans (step_coeff hg)
  have h : ∀ d, ∀ i < d, eCoeff f i = eCoeff g i := by
    intro d
    induction d with
    | zero => intro i hi; omega
    | succ d ih =>
      intro i hi
      rw [hf', hg']
      exact step_contract ih i hi
  exact eCoeff_ext (fun n => h (n + 1) n (by omega))

theorem unique_solution : ∃! f : PowerSeries ℚ,
    constantCoeff f = 0 ∧ f = X * (exp ℚ).subst (iterateComp f 4) := by
  exact ⟨A, A_equation, fun f hf => fixed_unique hf.1 A_equation.1 hf.2 A_equation.2⟩

end D5.S1.Recurrence.Residue.QuarticEGFFixedPoint
