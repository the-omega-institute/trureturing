/- GID: D5/S3/Quantum/Analysis/GazeauNormalRealization
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/GazeauNormalRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: No closed dense self-adjoint, skew-adjoint, or normal Gazeau realization. -/

import D5.S3.Quantum.Analysis.GaussianSchwartz
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.InnerProductSpace.LinearPMap

open MeasureTheory SchwartzMap

namespace D5.S3.Quantum.Analysis.GazeauNormalRealization

noncomputable section

abbrev ScalarL2 := MeasureTheory.Lp ℂ 2 (volume : MeasureTheory.Measure ℝ)
abbrev V := ScalarL2 × ScalarL2
abbrev Core := 𝓢(ℝ, ℂ) × 𝓢(ℝ, ℂ)

/-- The genuine Lebesgue almost-everywhere classes of both Schwartz components. -/
def embed (c : Core) : V :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume c.1,
   SchwartzMap.toLpCLM ℂ ℂ 2 volume c.2)

/-- The ordinary first-order block action on the entire Schwartz core. -/
def expression (c : Core) : Core :=
  (SchwartzMap.smulLeftCLM ℂ Complex.ofReal c.1 +
      Complex.I • SchwartzMap.derivCLM ℂ ℂ c.2,
   (-Complex.I) • SchwartzMap.derivCLM ℂ ℂ c.1 +
      SchwartzMap.smulLeftCLM ℂ Complex.ofReal c.2)

/-- Transport of every source graph pair by an algebraic complex-linear equivalence. -/
def sourceGraph {H : Type*} [AddCommGroup H] [Module ℂ H]
    (e : V ≃ₗ[ℂ] H) : Set (H × H) :=
  Set.range (fun c : Core => (e (embed c), e (embed (expression c))))

/-- No complete positive Hilbert structure admits any of the three adjoint
alternatives for a closed densely defined extension of the full source action. -/
theorem result (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (e : V ≃ₗ[ℂ] H) :
    ¬ ∃ T : H →ₗ.[ℂ] H,
      sourceGraph e ⊆ (T.graph : Set (H × H)) ∧
      Dense (T.domain : Set H) ∧ T.IsClosed ∧
      (T.adjoint = T ∨ T.adjoint = -T ∨
        ∀ x z : H,
          (∃ y : H, (x, y) ∈ T.graph ∧ (y, z) ∈ T.adjoint.graph) ↔
          (∃ y : H, (x, y) ∈ T.adjoint.graph ∧ (y, z) ∈ T.graph)) := by
  classical
  obtain ⟨gr, hgr⟩ := GaussianSchwartz.exists_gaussian_schwartz ℝ
  let g : 𝓢(ℝ, ℂ) := SchwartzMap.postcompCLM Complex.ofRealCLM gr
  let X := SchwartzMap.smulLeftCLM ℂ Complex.ofReal
  let xg : 𝓢(ℝ, ℂ) := X g
  have hg (x : ℝ) : g x = (Real.exp (-(2 : ℝ)⁻¹ * x ^ 2) : ℂ) := by
    simp [g, SchwartzMap.postcompCLM_apply, hgr, Real.norm_eq_abs, sq_abs]
  have hX (f : 𝓢(ℝ, ℂ)) (x : ℝ) : X f x = (x : ℂ) * f x := by
    simp [X, SchwartzMap.smulLeftCLM_apply_apply
      Function.Complex.hasTemperateGrowth_ofReal, smul_eq_mul]
  have hgd (x : ℝ) : HasDerivAt g (-(x : ℂ) * g x) x := by
    have hr : HasDerivAt (fun y : ℝ => Real.exp (-(2 : ℝ)⁻¹ * y ^ 2))
        (Real.exp (-(2 : ℝ)⁻¹ * x ^ 2) * (-x)) x := by
      convert (((hasDerivAt_id x).pow 2).const_mul (-(2 : ℝ)⁻¹)).exp using 1 <;> simp only [Pi.pow_apply, id_eq] <;> ring
    have hc := hr.ofReal_comp
    rw [← show (g : ℝ → ℂ) = (fun y : ℝ => (Real.exp (-(2 : ℝ)⁻¹ * y ^ 2) : ℂ))
      from funext hg] at hc
    convert hc using 1
    simp only [hg, Complex.ofReal_mul, Complex.ofReal_neg]
    ring
  have hxgd (x : ℝ) : HasDerivAt xg (g x - (x : ℂ) ^ 2 * g x) x := by
    have hx : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    have hh := hx.mul (hgd x)
    change HasDerivAt (fun y : ℝ => (y : ℂ) * g y)
      (1 * g x + (x : ℂ) * (-(x : ℂ) * g x)) x at hh
    rw [← show (xg : ℝ → ℂ) = (fun y : ℝ => (y : ℂ) * g y)
      from funext (hX g)] at hh
    convert hh using 1 <;> ring
  have dg : SchwartzMap.derivCLM ℂ ℂ g = -xg := by
    ext x
    simp only [SchwartzMap.derivCLM_apply, neg_apply]
    rw [(hgd x).deriv]
    change -(x : ℂ) * g x = -(X g x)
    rw [hX]
    ring
  have dxg : SchwartzMap.derivCLM ℂ ℂ xg = g - X xg := by
    ext x
    simp only [SchwartzMap.derivCLM_apply, sub_apply]
    rw [(hxgd x).deriv, hX]
    change g x - (x : ℂ) ^ 2 * g x = g x - (x : ℂ) * (X g x)
    rw [hX]
    ring
  let cv : Core := (g, (-Complex.I) • g)
  let cw : Core := (xg, (-Complex.I) • xg)
  have hcv : expression cv = 0 := by
    apply Prod.ext
    · ext x
      simp [expression, cv, X, map_smul, dg, xg, hX,
        smul_eq_mul] <;> ring_nf <;> simp [Complex.I_sq]
    · ext x
      simp [expression, cv, X, map_smul, dg, xg] <;> ring_nf <;> simp [Complex.I_sq]
  have hcw : expression cw = cv := by
    apply Prod.ext
    · ext x
      simp [expression, cw, cv, X, map_smul, dxg, xg, hX,
        smul_eq_mul] <;> ring_nf <;> simp [Complex.I_sq]
    · ext x
      simp [expression, cw, cv, X, map_smul, dxg, xg, hX,
        smul_eq_mul] <;> ring_nf <;> simp [Complex.I_sq]
  have hLp0 : (0 : 𝓢(ℝ, ℂ)).toLp 2 volume = 0 :=
    (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_zero
  have hembed0 : embed 0 = 0 := by
    change ((0 : 𝓢(ℝ, ℂ)).toLp 2 volume,
      (0 : 𝓢(ℝ, ℂ)).toLp 2 volume) = 0
    rw [hLp0]
    rfl
  let v : H := e (embed cv)
  let w : H := e (embed cw)
  have hv : v ≠ 0 := by
    intro hv0
    have he : embed cv = 0 := e.injective (by simpa [v] using hv0)
    have hp : g.toLp 2 volume = (0 : 𝓢(ℝ, ℂ)).toLp 2 volume := by
      simpa [embed, cv, hLp0] using congrArg Prod.fst he
    have hg0 : g = 0 := SchwartzMap.injective_toLp 2 volume hp
    have hpoint := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) hg0
    simp [hg] at hpoint
  rintro ⟨T, hgraph, hdense, _hclosed, halt⟩
  have hvg : (v, (0 : H)) ∈ T.graph := by
    have h := hgraph (Set.mem_range_self cv)
    simpa [hcv, hembed0, v] using h
  have hwg : (w, v) ∈ T.graph := by
    have h := hgraph (Set.mem_range_self cw)
    simpa [sourceGraph, hcw, v, w] using h
  obtain ⟨tv, htv, htv0⟩ := (T.mem_graph_iff).mp hvg
  obtain ⟨tw, htw, htwv⟩ := (T.mem_graph_iff).mp hwg
  have havg : (v, (0 : H)) ∈ T.adjoint.graph := by
    rcases halt with hself | hskew | hnormal
    · simpa [hself] using hvg
    · rw [hskew]
      apply ((-T).mem_graph_iff).mpr
      exact ⟨tv, htv, by simpa using congrArg Neg.neg htv0⟩
    · have hzero : ((0 : H), (0 : H)) ∈ T.adjoint.graph :=
        T.adjoint.graph.zero_mem
      obtain ⟨a, hva, ha0⟩ := (hnormal v 0).mp ⟨0, hvg, hzero⟩
      obtain ⟨av, hav, havalue⟩ := (T.adjoint.mem_graph_iff).mp hva
      obtain ⟨ta, hta, htaz⟩ := (T.mem_graph_iff).mp ha0
      have hi := T.adjoint_isFormalAdjoint hdense av ta
      have ha : a = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp (by
        calc
          inner ℂ a a = inner ℂ (T.adjoint av) (ta : H) := by rw [havalue, hta]
          _ = inner ℂ (av : H) (T ta) := hi
          _ = 0 := by rw [htaz, inner_zero_right])
      simpa [ha] using hva
  obtain ⟨av, hav, havalue⟩ := (T.adjoint.mem_graph_iff).mp havg
  have hi := T.adjoint_isFormalAdjoint hdense av tw
  have hvzero : v = 0 := (inner_self_eq_zero (𝕜 := ℂ)).mp (by
    calc
      inner ℂ v v = inner ℂ (av : H) (T tw) := by rw [hav, htwv]
      _ = inner ℂ (T.adjoint av) (tw : H) := hi.symm
      _ = 0 := by rw [havalue, inner_zero_left])
  exact hv hvzero

#print axioms result

end

end D5.S3.Quantum.Analysis.GazeauNormalRealization
