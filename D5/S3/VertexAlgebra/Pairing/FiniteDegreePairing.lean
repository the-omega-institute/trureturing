/- GID: D5/S3/VertexAlgebra/Pairing/FiniteDegreePairing
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/Pairing/FiniteDegreePairing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conditional finite-degree sesquilinear pairing and finite geometric pairing preservation. -/

import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Tactic

/-! Finite-support sesquilinear pairing and geometric inclusion isometry.

The full-telescope escape audit for every public theorem remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/25857
The issue is disclosure, not a validated registration or a BRST realization. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace D5.S3.VertexAlgebra.FiniteDegreePairing

variable {ι V : Type*} [AddCommGroup V] [Module ℂ V]

/-- This is support in a genuine basis of V, not a new state space. -/
def Supported (b : Module.Basis ι ℂ V) (P : ι → Prop) (x : V) : Prop :=
  ∀ i, b.repr x i ≠ 0 → P i

theorem expansion (b : Module.Basis ι ℂ V) (x : V) :
    (∑ i ∈ (b.repr x).support, b.repr x i • b i) = x := by
  classical
  simpa [Finsupp.linearCombination_apply, Finsupp.sum] using b.linearCombination_repr x

theorem supported_mono (b : Module.Basis ι ℂ V) {P Q : ι → Prop}
    {x : V} (hx : Supported b P x) (hPQ : ∀ i, P i → Q i) : Supported b Q x :=
  fun i hi => hPQ i (hx i hi)

theorem supported_smul (b : Module.Basis ι ℂ V) {P : ι → Prop}
    (c : ℂ) {x : V} (hx : Supported b P x) : Supported b P (c • x) := by
  intro i hi
  apply hx i
  intro hz
  exact hi (by simp [hz])

theorem supported_neg (b : Module.Basis ι ℂ V) {P : ι → Prop}
    {x : V} (hx : Supported b P x) : Supported b P (-x) := by
  simpa using supported_smul b (-1) hx

/-- A finite coefficient must come from an actual nonzero input coefficient. -/
theorem map_contribution (b : Module.Basis ι ℂ V) (A : Module.End ℂ V)
    (x : V) (j : ι) (hj : b.repr (A x) j ≠ 0) :
    ∃ i, b.repr x i ≠ 0 ∧ b.repr (A (b i)) j ≠ 0 := by
  classical
  have he : A x = ∑ i ∈ (b.repr x).support, b.repr x i • A (b i) := by
    conv_lhs => rw [← expansion b x]
    simp only [map_sum, map_smul]
  have hs : (∑ i ∈ (b.repr x).support,
      b.repr x i • b.repr (A (b i)) j) ≠ 0 := by
    simpa only [he, map_sum, map_smul, Finsupp.sum_apply, Finset.sum_apply',
      Finsupp.smul_apply] using hj
  obtain ⟨i, hi, hci⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  refine ⟨i, Finsupp.mem_support_iff.mp hi, ?_⟩
  intro hz
  exact hci (by rw [hz, smul_zero])

theorem map_supported (b : Module.Basis ι ℂ V) (A : Module.End ℂ V)
    {P Q : ι → Prop} {x : V} (hx : Supported b P x)
    (hA : ∀ i j, P i → b.repr (A (b i)) j ≠ 0 → Q j) :
    Supported b Q (A x) := by
  intro j hj
  obtain ⟨i, hi, hij⟩ := map_contribution b A x j hj
  exact hA i j (hx i hi) hij

/-- Finite double expansion with conjugation in the first slot. -/
theorem form_expansion (b : Module.Basis ι ℂ V)
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (x y : V) :
    H x y = ∑ i ∈ (b.repr x).support, ∑ j ∈ (b.repr y).support,
      star (b.repr x i) * b.repr y j * H (b i) (b j) := by
  classical
  conv_lhs => rw [← expansion b x, ← expansion b y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
    starRingEnd_apply, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem supported_orthogonal (b : Module.Basis ι ℂ V)
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) {P Q : ι → Prop} {x y : V}
    (hx : Supported b P x) (hy : Supported b Q y)
    (hPQ : ∀ i j, P i → Q j → H (b i) (b j) = 0) : H x y = 0 := by
  classical
  rw [form_expansion b H x y]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  rw [hPQ i j (hx i (Finsupp.mem_support_iff.mp hi))
    (hy j (Finsupp.mem_support_iff.mp hj)), mul_zero]

/-- An application must supply the signed-degree selection law.
No realization of this hypothesis for the original BRST operators is asserted. -/
theorem lower_bounds_orthogonal (b : Module.Basis ι ℂ V) (d : ι → ℤ)
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hH : ∀ i j, d i + d j ≠ 0 → H (b i) (b j) = 0)
    {a c : ℤ} {x y : V} (hx : Supported b (fun i => a ≤ d i) x)
    (hy : Supported b (fun j => c ≤ d j) y) (hac : 0 < a + c) : H x y = 0 := by
  apply supported_orthogonal b H hx hy
  intro i j hi hj
  apply hH i j
  omega

/-- Charge/sector restrictions are retained while iterating the actual map. -/
theorem raising_power_support (b : Module.Basis ι ℂ V) (d : ι → ℤ)
    (sector : ι → Prop) (A : Module.End ℂ V)
    (hA : ∀ i j, sector i → b.repr (A (b i)) j ≠ 0 →
      sector j ∧ d i + 1 ≤ d j)
    {x : V} (hx : Supported b (fun i => sector i ∧ d i = 0) x) (r : ℕ) :
    Supported b (fun i => sector i ∧ (r : ℤ) ≤ d i) (((-A)^r) x) := by
  induction r with
  | zero =>
    simpa using supported_mono b hx (fun i hi => ⟨hi.1, by omega⟩)
  | succ r ih =>
    rw [pow_succ', Module.End.mul_apply]
    have hsupport : Supported b (fun i => sector i ∧ (↑(r + 1) : ℤ) ≤ d i)
        (A (((-A)^r) x)) := by
      refine map_supported (P := fun i => sector i ∧ (r : ℤ) ≤ d i)
        (Q := fun i => sector i ∧ (↑(r + 1) : ℤ) ≤ d i) b A ih ?_
      intro i j hi hij
      obtain ⟨hj, hd⟩ := hA i j hi.1 hij
      exact ⟨hj, by push_cast; omega⟩
    simpa using supported_neg b hsupport

/-- Every cross term except (0,0) is zero; no inverse or nilpotence needed. -/
theorem powers_orthogonal (b : Module.Basis ι ℂ V) (d : ι → ℤ)
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hH : ∀ i j, d i + d j ≠ 0 → H (b i) (b j) = 0)
    (sector : ι → Prop) (A : Module.End ℂ V)
    (hA : ∀ i j, sector i → b.repr (A (b i)) j ≠ 0 →
      sector j ∧ d i + 1 ≤ d j)
    {x y : V} (hx : Supported b (fun i => sector i ∧ d i = 0) x)
    (hy : Supported b (fun i => sector i ∧ d i = 0) y)
    (r s : ℕ) (hrs : 0 < r + s) : H (((-A)^r) x) (((-A)^s) y) = 0 := by
  apply lower_bounds_orthogonal b d H hH
    (supported_mono b (raising_power_support b d sector A hA hx r) (fun _ h => h.2))
    (supported_mono b (raising_power_support b d sector A hA hy s) (fun _ h => h.2))
  exact_mod_cast hrs

theorem finite_inclusion_isometry (b : Module.Basis ι ℂ V) (d : ι → ℤ)
    (H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ)
    (hH : ∀ i j, d i + d j ≠ 0 → H (b i) (b j) = 0)
    (sector : ι → Prop) (A : Module.End ℂ V)
    (hA : ∀ i j, sector i → b.repr (A (b i)) j ≠ 0 →
      sector j ∧ d i + 1 ≤ d j)
    {x y : V} (hx : Supported b (fun i => sector i ∧ d i = 0) x)
    (hy : Supported b (fun i => sector i ∧ d i = 0) y)
    (n : ℕ) (hn : 1 ≤ n) :
    H ((∑ r ∈ Finset.range n, (-A)^r) x)
      ((∑ s ∈ Finset.range n, (-A)^s) y) = H x y := by
  classical
  simp only [LinearMap.sum_apply, map_sum]
  rw [Finset.sum_eq_single 0]
  · rw [Finset.sum_eq_single 0]
    · simp
    · intro s hs hs0
      exact powers_orthogonal b d H hH sector A hA hx hy s 0 (by omega)
    · intro h0
      exact False.elim (h0 (Finset.mem_range.mpr (by omega)))
  · intro r hr hr0
    apply Finset.sum_eq_zero
    intro s hs
    exact powers_orthogonal b d H hH sector A hA hx hy s r (by omega)
  · intro h0
    exact False.elim (h0 (Finset.mem_range.mpr (by omega)))

end D5.S3.VertexAlgebra.FiniteDegreePairing
