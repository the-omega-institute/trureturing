/- GID: D5/S3/Observer/Linear/GainRayNuisance
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayNuisance
   mirror-E: none(waiver:trace-kernel-nuisance-geometry)
   anchors: [mathlib/module/Mathlib.Algebra.Module.Submodule.Union]
   utility: none
   digest: Trace restriction and weighted evaluations identify the nuisance directions of a scalar readout. -/

import D5.S3.Observer.Linear.GainRayScalarIdentity
import D5.S3.Observer.Linear.GainRayShortWord
import D5.S3.Observer.Linear.GainRayMixedGeometry
import D5.S3.Observer.Linear.GainRayWordGeometry
import D5.S3.Observer.Linear.GainRaySuccessPolynomial
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.Matrix.Rank

set_option autoImplicit false
noncomputable section
open scoped Matrix Classical
namespace D5.S3.Observer.Linear.GainRay

/-- The trace observation retains the entire auxiliary matrix, without positivity restrictions. -/
def traceObservation (A : Mat) : Mat →ₗ[ℝ] ℝ where
  toFun S := Matrix.trace (A * S)
  map_add' S T := by simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' a S := by simp [Matrix.mul_smul, Matrix.trace_smul]

private theorem trace_observation_injective : Function.Injective traceObservation := by
  intro A B h
  exact Matrix.ext_iff_trace_mul_right.mpr (fun S => congrArg (fun f : Mat →ₗ[ℝ] ℝ => f S) h)

/-- The representative is computed from the actual zeroth row and original prefixes. -/
def scalarRepresentative (d : ℕ) (w : List Bool) (C : Readout d w) : Mat :=
  ∑ i : Fin (w.length+1), C 0 i • acquisition (w.take i.val)

private theorem scalar_representative_trace (d : ℕ) (w : List Bool) (C : Readout d w) :
    traceObservation (scalarRepresentative d w C) = scalarFunctional d w C := by
  ext S
  simp [traceObservation, scalarRepresentative, scalarFunctional, response,
    responseMatrix, Matrix.mul_apply, Matrix.sum_mul, Matrix.trace_sum,
    Matrix.smul_mul, Matrix.trace_smul]

private theorem restriction_zero_iff (ell : Mat →ₗ[ℝ] ℝ) (L A : Mat)
    (hL : traceObservation L = ell) :
    (∀ S : Mat, ell S = 0 → traceObservation A S = 0) ↔ ∃ c : ℝ, A = c • L := by
  constructor
  · intro h
    have hm : traceObservation A ∈ Submodule.span ℝ ({ell} : Set (Mat →ₗ[ℝ] ℝ)) := by
      have hx := mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => ell)
        (K := traceObservation A) (by
          rw [iInf_const]
          intro S hS
          exact h S hS)
      simpa using hx
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    refine ⟨c, trace_observation_injective ?_⟩
    ext S
    have he := congrArg (fun f : Mat →ₗ[ℝ] ℝ => f S) hc
    simpa [traceObservation, Matrix.smul_mul, Matrix.trace_smul, ← hL] using he.symm
  · rintro ⟨c, rfl⟩ S hS
    simp [traceObservation, Matrix.smul_mul, Matrix.trace_smul,
      show Matrix.trace (L*S) = 0 by change traceObservation L S = 0; rw [hL]; exact hS]

/-- A single element of the actual scalar kernel realizes exactly the proportionality zeros. -/
theorem scalar_kernel_source (d : ℕ) (w : List Bool) (C : Readout d w)
    (hell : scalarFunctional d w C ≠ 0) :
    scalarRepresentative d w C ≠ 0 ∧
    (∀ T : Mat, Matrix.trace (scalarRepresentative d w C * T) = scalarFunctional d w C T) ∧
    ∃ S : Mat, scalarFunctional d w C S = 0 ∧
      ∀ i : Fin (w.length+1), Matrix.trace (acquisition (w.take i.val) * S) = 0 ↔
        ∃ c : ℝ, acquisition (w.take i.val) = c • scalarRepresentative d w C := by
  classical
  let ell := scalarFunctional d w C
  let L := scalarRepresentative d w C
  have hL : traceObservation L = ell := scalar_representative_trace d w C
  have hn : L ≠ 0 := by
    intro hz
    apply hell
    change ell = 0
    rw [← hL, hz]
    ext T
    simp [traceObservation]
  let Q (i : Fin (w.length+1)) : Prop :=
    ∃ c : ℝ, acquisition (w.take i.val) = c • L
  have hex (i : {i : Fin (w.length+1) // ¬ Q i}) :
      ∃ S ∈ LinearMap.ker ell, traceObservation (acquisition (w.take i.val.val)) S ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact i.property ((restriction_zero_iff ell L _ hL).mp hh)
  obtain ⟨S, hS, ha⟩ := Module.Dual.exists_forall_mem_ne_zero_of_forall_exists
    (LinearMap.ker ell) (fun i : {i : Fin (w.length+1) // ¬ Q i} =>
      traceObservation (acquisition (w.take i.val.val))) hex
  refine ⟨hn, fun T => congrArg (fun f : Mat →ₗ[ℝ] ℝ => f T) hL, S, hS, ?_⟩
  intro i
  constructor
  · intro hz
    by_contra hq
    exact ha ⟨i,hq⟩ hz
  · intro hq
    exact (restriction_zero_iff ell L _ hL).mpr hq S hS

#print axioms scalar_kernel_source

/-- Multiplication by arbitrary clock weights retains exactly the available evaluation rank. -/
theorem weighted_evaluation_rank (d n : ℕ) (t : Fin n → ℝ)
    (ht : Function.Injective t) (a : Fin n → ℝ) :
    Matrix.rank (fun i k => a i * t i ^ k.val : Matrix (Fin n) (Fin (d+1)) ℝ) =
      min (Finset.univ.filter (fun i => a i ≠ 0)).card (d+1) := by
  classical
  let U : Finset (Fin n) := Finset.univ.filter (fun i => a i ≠ 0)
  let r := min U.card (d+1)
  obtain ⟨K,hKU,hK⟩ := Finset.exists_subset_card_eq (show r ≤ U.card from min_le_left _ _)
  let e : Fin K.card ≃ K := K.equivFin.symm
  let f : Fin K.card → Fin n := fun j => (e j).val
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  have ha (j : Fin K.card) : a (f j) ≠ 0 := (Finset.mem_filter.mp (hKU (e j).property)).2
  let B : Matrix (Fin n) (Fin (d+1)) ℝ := fun i k => a i * t i ^ k.val
  have hs : Function.Surjective (B.submatrix f id).mulVec := by
    intro y
    obtain ⟨β,hβ⟩ := evaluation_surjective d K.card (t ∘ f) (ht.comp hf)
      (by rw [hK]; exact min_le_right _ _) (fun j => y j / a (f j))
    refine ⟨β, ?_⟩
    ext j
    have he := congrFun hβ j
    change (∑ k : Fin (d+1), (a (f j) * t (f j)^k.val) * β k) = y j
    simp only [evaluate, evaluation, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Function.comp_apply] at he
    rw [show (∑ k : Fin (d+1), (a (f j) * t (f j)^k.val) * β k) =
        a (f j) * ∑ k : Fin (d+1), t (f j)^k.val * β k by rw [Finset.mul_sum]; congr 1; ext k; ring,
      he, mul_div_cancel₀ _ (ha j)]
  have hl : r ≤ B.rank := by
    have hr : (B.submatrix f id).rank = K.card := by
      rw [Matrix.rank, LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_pi]
      simp
    rw [← hK, ← hr]
    exact Matrix.rank_submatrix_le B f id
  apply le_antisymm _ hl
  apply le_min
  · apply Matrix.rank_le_card_of_support_subset B U
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hz
    apply hi
    ext k
    change a i * t i ^ k.val = 0
    rw [hz, zero_mul]
  · exact Matrix.rank_le_width B

#print axioms weighted_evaluation_rank

private theorem scalar_readout_surjective (d : ℕ) (w : List Bool) (C : Readout d w)
    (ell : Mat →ₗ[ℝ] ℝ) (hell : ell ≠ 0)
    (he : ∀ T : Mat, response d w C T = ell T • (1 : Matrix _ _ ℝ)) :
    Function.Surjective C.mulVec := by
  obtain ⟨S,hS⟩ : ∃ S : Mat, ell S ≠ 0 := by
    by_contra hh
    push_neg at hh
    exact hell (LinearMap.ext hh)
  intro y
  refine ⟨(responseMatrix d w S).mulVec ((ell S)⁻¹ • y), ?_⟩
  rw [Matrix.mulVec_mulVec]
  change (response d w C S).mulVec ((ell S)⁻¹ • y) = y
  rw [he, Matrix.smul_mulVec, Matrix.one_mulVec, smul_inv_smul₀ hS]

private theorem response_range_le_kernel (d : ℕ) (w : List Bool) (C : Readout d w)
    (ell : Mat →ₗ[ℝ] ℝ)
    (he : ∀ T : Mat, response d w C T = ell T • (1 : Matrix _ _ ℝ))
    (S : Mat) (hS : ell S = 0) :
    LinearMap.range (responseMatrix d w S).mulVecLin ≤ LinearMap.ker C.mulVecLin := by
  rintro _ ⟨β,rfl⟩
  change C.mulVec ((responseMatrix d w S).mulVec β) = 0
  rw [Matrix.mulVec_mulVec]
  change (response d w C S).mulVec β = 0
  rw [he,hS,zero_smul,Matrix.zero_mulVec]

/-- A nowhere-zero nuisance in the scalar kernel forces the exact twice-dimension endpoint. -/
theorem scalar_kernel_endpoint (d : ℕ) (w : List Bool) (C : Readout d w)
    (ell : Mat →ₗ[ℝ] ℝ) (hell : ell ≠ 0)
    (he : ∀ T : Mat, response d w C T = ell T • (1 : Matrix _ _ ℝ))
    (hN : w.length+1 ≤ 2*(d+1)) (S : Mat) (hS : ell S = 0)
    (ha : ∀ i : Fin (w.length+1), Matrix.trace (acquisition (w.take i.val)*S) ≠ 0) :
    w.length+1 = 2*(d+1) ∧
      LinearMap.ker C.mulVecLin = LinearMap.range (responseMatrix d w S).mulVecLin := by
  classical
  have hsurj := scalar_readout_surjective d w C ell hell he
  have hrC : Module.finrank ℝ (LinearMap.range C.mulVecLin) = d+1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi]
    simp
  have hdim := C.mulVecLin.finrank_range_add_finrank_ker
  simp only [Module.finrank_pi, Fintype.card_fin, Module.finrank_self, mul_one, hrC] at hdim
  have hn : d+1 ≤ w.length+1 := by omega
  have ht : Function.Injective (clocks (w.length+1)) := by
    intro i j h
    apply Fin.ext
    dsimp [clocks] at h
    exact_mod_cast h
  have hrH : Module.finrank ℝ (LinearMap.range (responseMatrix d w S).mulVecLin) = d+1 := by
    have hh := weighted_evaluation_rank d (w.length+1) (clocks (w.length+1)) ht
      (fun i => Matrix.trace (acquisition (w.take i.val)*S))
    have hf : Finset.univ.filter (fun i : Fin (w.length+1) =>
        Matrix.trace (acquisition (w.take i.val)*S) ≠ 0) = Finset.univ := by
      ext i
      simp [ha i]
    change Module.finrank ℝ (LinearMap.range (responseMatrix d w S).mulVecLin) =
      min (Finset.univ.filter (fun i : Fin (w.length+1) =>
        Matrix.trace (acquisition (w.take i.val)*S) ≠ 0)).card (d+1) at hh
    simpa only [hf, Finset.card_univ, Fintype.card_fin, Nat.min_eq_right hn] using hh
  have hle := response_range_le_kernel d w C ell he S hS
  have hbound := Submodule.finrank_mono hle
  refine ⟨by omega, ?_⟩
  exact (Submodule.eq_of_le_of_finrank_le hle (by omega)).symm

/-- At that endpoint every other scalar-kernel source induces a scalar trace ratio. -/
theorem scalar_kernel_ratios (d : ℕ) (hd : 1 ≤ d) (w : List Bool) (C : Readout d w)
    (ell : Mat →ₗ[ℝ] ℝ) (hell : ell ≠ 0)
    (he : ∀ T : Mat, response d w C T = ell T • (1 : Matrix _ _ ℝ))
    (hN : w.length+1 ≤ 2*(d+1)) (S : Mat) (hS : ell S = 0)
    (ha : ∀ i : Fin (w.length+1), Matrix.trace (acquisition (w.take i.val)*S) ≠ 0) :
    ∀ T : Mat, ell T = 0 → ∀ i j : Fin (w.length+1),
      Matrix.trace (acquisition (w.take i.val)*T) / Matrix.trace (acquisition (w.take i.val)*S) =
      Matrix.trace (acquisition (w.take j.val)*T) / Matrix.trace (acquisition (w.take j.val)*S) := by
  obtain ⟨hend,hker⟩ := scalar_kernel_endpoint d w C ell hell he hN S hS ha
  intro T hT
  apply diagonal_evaluation_rigid d (w.length+1) (by omega) (clocks (w.length+1))
    (by intro i j h; apply Fin.ext; dsimp [clocks] at h; exact_mod_cast h)
  intro p hp
  let β := Polynomial.toFn (d+1) p
  have hpβ : gain d β = p := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)
  have hm := response_range_le_kernel d w C ell he T hT
    (show (responseMatrix d w T).mulVec β ∈ LinearMap.range (responseMatrix d w T).mulVecLin
      from ⟨β,rfl⟩)
  rw [hker] at hm
  obtain ⟨γ,hγ⟩ := hm
  refine ⟨gain d γ, ?_, ?_⟩
  · change (Polynomial.ofFn (d+1) γ).natDegree ≤ d
    exact Nat.le_of_lt_succ (Polynomial.ofFn_natDegree_lt (by omega : 1 ≤ d+1) γ)
  · intro i
    have hresponse (U : Mat) (b : Coeff d) :
        (responseMatrix d w U).mulVec b i =
          Matrix.trace (acquisition (w.take i.val)*U) * (gain d b).eval (clocks (w.length+1) i) := by
      rw [← evaluation_polynomial]
      simp [responseMatrix, Matrix.mulVec, dotProduct, evaluate, evaluation, clocks,
        Finset.mul_sum, mul_assoc]
    have hh := congrFun hγ i
    change (responseMatrix d w S).mulVec γ i = (responseMatrix d w T).mulVec β i at hh
    rw [hresponse, hresponse, hpβ] at hh
    change (gain d γ).eval (clocks (w.length+1) i) =
      (Matrix.trace (acquisition (w.take i.val)*T) / Matrix.trace (acquisition (w.take i.val)*S)) *
        p.eval (clocks (w.length+1) i)
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff (ha i)).mpr
    simpa [mul_comm] using hh
#print axioms scalar_kernel_endpoint
#print axioms scalar_kernel_ratios

/-- The endpoint ratio law bounds the actual cumulative matrix span by two. -/
theorem scalar_kernel_span_le_two (d : ℕ) (hd : 1 ≤ d) (w : List Bool) (C : Readout d w)
    (hell : scalarFunctional d w C ≠ 0)
    (he : ∀ T : Mat, response d w C T = scalarFunctional d w C T • (1 : Matrix _ _ ℝ))
    (hN : w.length+1 ≤ 2*(d+1)) (S : Mat) (hS : scalarFunctional d w C S = 0)
    (ha : ∀ i : Fin (w.length+1), Matrix.trace (acquisition (w.take i.val)*S) ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))) ≤ 2 := by
  let i0 : Fin (w.length+1) := ⟨0,by omega⟩
  let A0 := acquisition (w.take i0.val)
  let L := scalarRepresentative d w C
  let K := Submodule.span ℝ ({L,A0} : Set Mat)
  have hle : Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val))) ≤ K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    let r := Matrix.trace (acquisition (w.take i.val)*S) / Matrix.trace (A0*S)
    have hvan : ∀ T : Mat, scalarFunctional d w C T = 0 →
        traceObservation (acquisition (w.take i.val) - r • A0) T = 0 := by
      intro T hT
      have hh := scalar_kernel_ratios d hd w C _ hell he hN S hS ha T hT i i0
      dsimp [i0] at hh
      dsimp [traceObservation]
      rw [Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul]
      change Matrix.trace (acquisition (w.take i.val)*T) -
        (Matrix.trace (acquisition (w.take i.val)*S) / Matrix.trace (A0*S)) *
        Matrix.trace (A0*T) = 0
      have hi := ha i
      have h0 := ha i0
      change Matrix.trace (acquisition (w.take i.val)*T) /
          Matrix.trace (acquisition (w.take i.val)*S) =
        Matrix.trace (A0*T) / Matrix.trace (A0*S) at hh
      change Matrix.trace (A0*S) ≠ 0 at h0
      field_simp [hi,h0] at hh ⊢
      nlinarith
    obtain ⟨c,hc⟩ := (restriction_zero_iff _ L _ (scalar_representative_trace d w C)).mp hvan
    have hx : acquisition (w.take i.val) = c • L + r • A0 := by
      rw [← hc]
      module
    change acquisition (w.take i.val) ∈ K
    rw [hx]
    exact K.add_mem (K.smul_mem _ (Submodule.subset_span (by simp)))
      (K.smul_mem _ (Submodule.subset_span (by simp)))
  have hb : Module.finrank ℝ K ≤ 2 := by
    have hh := finrank_span_le_card (R := ℝ) ({L,A0} : Set Mat)
    apply hh.trans
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  exact (Submodule.finrank_mono hle).trans hb

#print axioms scalar_kernel_span_le_two

/-- Every mixed Boolean word is obstructed through twice the whole coefficient dimension. -/
theorem mixed_scalar_obstruction (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (hM : false ∈ w) (hJ : true ∈ w) (hN : w.length+1 ≤ 2*(d+1))
    (C : Readout d w) (hb : C.mulVec (fun _ => 1) = 0)
    (he : ∀ T : Mat, response d w C T = scalarFunctional d w C T • (1 : Matrix _ _ ℝ)) :
    scalarFunctional d w C = 0 := by
  classical
  by_contra hell
  obtain ⟨hL,htrace,S,hS,hpattern⟩ := scalar_kernel_source d w C hell
  let a : Fin (w.length+1) → ℝ := fun i => Matrix.trace (acquisition (w.take i.val)*S)
  let Q : Finset (Fin (w.length+1)) := Finset.univ.filter (fun i => a i = 0)
  have hq : Q.card ≤ d+1 := by
    have hQ : Q = Finset.univ.filter (fun i : Fin (w.length+1) =>
        ∃ c : ℝ, acquisition (w.take i.val) = c • scalarRepresentative d w C) := by
      ext i
      simp only [Q,Finset.mem_filter,Finset.mem_univ,true_and,a,hpattern]
    rw [hQ]
    exact (cumulative_proportionality_card w _).trans (by omega)
  by_cases hq0 : Q.card = 0
  · have ha : ∀ i : Fin (w.length+1), a i ≠ 0 := by
      intro i hz
      have hm : i ∈ Q := by simp [Q,hz]
      rw [Finset.card_eq_zero.mp hq0] at hm
      exact Finset.notMem_empty _ hm
    have hh := scalar_kernel_span_le_two d hd w C hell he hN S hS ha
    have hthree := mixed_cumulative_span w hM hJ
    omega
  · obtain ⟨i0,hi0⟩ := Finset.card_pos.mp (by omega : 0 < Q.card)
    have hz : a i0 = 0 := (Finset.mem_filter.mp hi0).2
    have hsurj := scalar_readout_surjective d w C _ hell he
    have hrC : Module.finrank ℝ (LinearMap.range C.mulVecLin) = d+1 := by
      rw [LinearMap.range_eq_top.mpr hsurj,finrank_top,Module.finrank_pi]
      simp
    have hdim := C.mulVecLin.finrank_range_add_finrank_ker
    simp only [hrC,Module.finrank_pi,Fintype.card_fin,Module.finrank_self,mul_one] at hdim
    let H := LinearMap.range (responseMatrix d w S).mulVecLin
    let K := LinearMap.ker C.mulVecLin
    have hle : H ≤ K := response_range_le_kernel d w C _ he S hS
    have hnot : (fun _ : Fin (w.length+1) => (1 : ℝ)) ∉ H := by
      rintro ⟨β,hβ⟩
      have hh := congrFun hβ i0
      have hzero : Matrix.trace (acquisition (w.take i0.val)*S) = 0 := hz
      simp [responseMatrix,Matrix.mulVec,dotProduct,hzero] at hh
    have hlt : H < K := lt_of_le_of_ne hle (by
      intro heq
      apply hnot
      rw [heq]
      exact hb)
    have hstrict := Submodule.finrank_lt_finrank_of_lt hlt
    have ht : Function.Injective (clocks (w.length+1)) := by
      intro i j h
      apply Fin.ext
      dsimp [clocks] at h
      exact_mod_cast h
    have hr := weighted_evaluation_rank d (w.length+1) (clocks (w.length+1)) ht a
    have hc := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun i : Fin (w.length+1) => a i = 0)
    simp only [Finset.card_univ,Fintype.card_fin] at hc
    change Q.card + (Finset.univ.filter (fun i : Fin (w.length+1) => a i ≠ 0)).card = w.length+1 at hc
    change Module.finrank ℝ H = min (Finset.univ.filter (fun i => a i ≠ 0)).card (d+1) at hr
    rw [hr] at hstrict
    dsimp only [K] at hstrict
    omega

/-- For each actually successful mixed pair, a genuine nonzero native chart polynomial exists. -/
theorem mixed_chart_success_certificate (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (hM : false ∈ w) (hJ : true ∈ w) (hN : w.length+1 ≤ 2*(d+1))
    (C : Readout d w) (W : World d) (hW : Succeeds W w C) :
    ∃ j k : Fin (d+1), chartWedge d w C j k ≠ 0 ∧
      (∀ x r : ℝ, ∀ hx : 0 < x, ∀ hr : 0 < r, ∀ β : Coeff d, ∀ hn : β ≠ 0,
        ∀ δ : ℝ, Succeeds (chartWorld d x r hx hr β hn δ) w C →
          MvPolynomial.eval (chartParameters d x r β δ) (chartWedge d w C j k) = 0) ∧
      (∀ᵐ a : Fin (d+4) → ℝ ∂MeasureTheory.volume,
        MvPolynomial.eval a (chartWedge d w C j k) ≠ 0) := by
  apply chart_success_certificate
  intro hu
  obtain ⟨hb,he⟩ := universal_scalar_identity d hd w C hu
  by_cases hshort : w.length+1 ≤ d+1
  · exact short_word_no_universal_success d hd w hshort C hu W hW
  · have hn := successful_scalar_nonzero w C hb he W hW
    have hz := mixed_scalar_obstruction d hd w hM hJ hN C hb he
    exact hn (by rw [hz]; rfl)

#print axioms mixed_scalar_obstruction
#print axioms mixed_chart_success_certificate
end D5.S3.Observer.Linear.GainRay
