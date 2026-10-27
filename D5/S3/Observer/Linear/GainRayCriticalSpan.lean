/- GID: D5/S3/Observer/Linear/GainRayCriticalSpan
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/GainRayCriticalSpan
   mirror-E: none(waiver:critical-native-scalar-span)
   anchors: []
   utility: none
   digest: Clock multiplication grows a full-support observation space and bounds critical scalar identities. -/

import D5.S3.Observer.Linear.GainRayNuisance

set_option autoImplicit false
noncomputable section
open scoped Matrix
namespace D5.S3.Observer.Linear.GainRay

private def clockMultiply {ι : Type*} (t : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun v i := t i * v i
  map_add' _ _ := by ext i; simp [mul_add]
  map_smul' _ _ := by ext i; simp [mul_left_comm]

private def clockClosure {ι : Type*} (t : ι → ℝ) (V : Submodule ℝ (ι → ℝ)) :
    ℕ → Submodule ℝ (ι → ℝ)
  | 0 => V
  | k+1 => clockClosure t V k ⊔ (clockClosure t V k).map (clockMultiply t)

private theorem clockClosure_contains {ι : Type*} (t : ι → ℝ)
    (V : Submodule ℝ (ι → ℝ)) (k : ℕ) : V ≤ clockClosure t V k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih => exact ih.trans le_sup_left

private theorem clockClosure_le {ι : Type*} (t : ι → ℝ)
    (V K : Submodule ℝ (ι → ℝ)) (k : ℕ)
    (h : ∀ v ∈ V, ∀ j ≤ k, (fun i => v i * t i ^ j) ∈ K) :
    clockClosure t V k ≤ K := by
  induction k generalizing K with
  | zero =>
    intro v hv
    simpa using h v hv 0 le_rfl
  | succ k ih =>
    apply sup_le
    · exact ih K (fun v hv j hj => h v hv j (by omega))
    · apply Submodule.map_le_iff_le_comap.mpr
      apply ih
      intro v hv j hj
      change (fun i => t i * (v i * t i ^ j)) ∈ K
      convert h v hv (j+1) (by omega) using 1
      ext i
      simp [pow_succ]
      ring

private theorem invariant_full_support_top {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : Function.Injective t) (W : Submodule ℝ (ι → ℝ))
    (a : ι → ℝ) (ha : a ∈ W) (hna : ∀ i, a i ≠ 0)
    (hstable : W.map (clockMultiply t) ≤ W) : W = ⊤ := by
  classical
  have hpowers (k : ℕ) : (fun i => a i * t i ^ k) ∈ W := by
    induction k with
    | zero => simpa using ha
    | succ k ih =>
      have hh := hstable (Submodule.mem_map_of_mem ih)
      change (fun i => t i * (a i * t i ^ k)) ∈ W at hh
      convert hh using 1
      ext i
      simp [pow_succ]
      ring
  apply top_unique
  intro y _
  let p := Lagrange.interpolate (Finset.univ : Finset ι) t (fun i => y i / a i)
  have he (i : ι) : p.eval (t i) = y i / a i :=
    Lagrange.eval_interpolate_at_node _ (fun _ _ _ _ h => ht h) (Finset.mem_univ i)
  have hm : (fun i => a i * p.eval (t i)) ∈ W := by
    have hs := W.sum_mem (fun k (_ : k ∈ Finset.range (p.natDegree+1)) =>
      W.smul_mem (p.coeff k) (hpowers k))
    convert hs using 1
    ext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Polynomial.eval_eq_sum_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  convert hm using 1
  ext i
  rw [he, mul_div_cancel₀ _ (hna i)]

/-- Polynomial multiples of a full-support subspace gain one dimension per degree until full. -/
theorem weighted_polynomial_span_growth {ι : Type*} [Fintype ι]
    (t : ι → ℝ) (ht : Function.Injective t) (V K : Submodule ℝ (ι → ℝ))
    (a : ι → ℝ) (ha : a ∈ V) (hna : ∀ i, a i ≠ 0) (d : ℕ)
    (h : ∀ v ∈ V, ∀ j ≤ d, (fun i => v i * t i ^ j) ∈ K) :
    min (Fintype.card ι) (Module.finrank ℝ V + d) ≤ Module.finrank ℝ K := by
  have hg (k : ℕ) : min (Fintype.card ι) (Module.finrank ℝ V + k) ≤
      Module.finrank ℝ (clockClosure t V k) := by
    induction k with
    | zero =>
      change min (Fintype.card ι) (Module.finrank ℝ V + 0) ≤ Module.finrank ℝ V
      exact Nat.min_le_right _ _
    | succ k ih =>
      let W := clockClosure t V k
      by_cases hw : W = ⊤
      · have htop : clockClosure t V (k+1) = ⊤ := by
          change W ⊔ W.map (clockMultiply t) = ⊤
          rw [hw, top_sup_eq]
        change min (Fintype.card ι) (Module.finrank ℝ V + (k+1)) ≤
          Module.finrank ℝ (clockClosure t V (k+1))
        rw [htop, finrank_top]
        simp only [Module.finrank_pi, Module.finrank_self, mul_one]
        exact Nat.min_le_left _ _
      · have hlt : W < W ⊔ W.map (clockMultiply t) := by
          apply lt_of_le_of_ne le_sup_left
          intro heq
          apply hw
          exact invariant_full_support_top t ht W a (clockClosure_contains t V k ha) hna
            ((le_sup_right : W.map (clockMultiply t) ≤ W ⊔ W.map (clockMultiply t)).trans heq.ge)
        have hh := Submodule.finrank_lt_finrank_of_lt hlt
        have hn : Module.finrank ℝ W < Fintype.card ι := by
          have hh' := Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hw)
          simpa using hh'
        change min (Fintype.card ι) (Module.finrank ℝ V + (k+1)) ≤
          Module.finrank ℝ ↥(W ⊔ W.map (clockMultiply t))
        change min (Fintype.card ι) (Module.finrank ℝ V + k) ≤ Module.finrank ℝ W at ih
        omega
  exact (hg d).trans (Submodule.finrank_mono (clockClosure_le t V K d h))

#print axioms weighted_polynomial_span_growth

/-- At the critical original-clock budget a mixed nonzero scalar identity has span exactly three. -/
theorem critical_scalar_span (d : ℕ) (hd : 1 ≤ d) (w : List Bool)
    (hM : false ∈ w) (hJ : true ∈ w) (hN : w.length+1 = 2*(d+1)+1)
    (C : Readout d w) (hb : C.mulVec (fun _ => 1) = 0)
    (he : ∀ T : Mat, response d w C T = scalarFunctional d w C T • (1 : Matrix _ _ ℝ))
    (hell : scalarFunctional d w C ≠ 0) :
    Module.finrank ℝ (Submodule.span ℝ
      (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))) = 3 := by
  classical
  let H := Submodule.span ℝ
    (Set.range (fun i : Fin (w.length+1) => acquisition (w.take i.val)))
  have hthree : 3 ≤ Module.finrank ℝ H := mixed_cumulative_span w hM hJ
  apply le_antisymm _ hthree
  by_contra hbad
  have hmat : Module.finrank ℝ Mat = 4 := by
    simpa using (Module.finrank_matrix (R := ℝ) (M := ℝ) (Fin 2) (Fin 2))
  have hfour : Module.finrank ℝ H = 4 := by
    have hh := H.finrank_le
    rw [hmat] at hh
    omega
  have hfull : H = ⊤ := Submodule.eq_top_of_finrank_eq (hfour.trans hmat.symm)
  have separates (S : Mat)
      (hz : ∀ i : Fin (w.length+1), Matrix.trace (acquisition (w.take i.val)*S) = 0) :
      S = 0 := by
    apply Matrix.ext_iff_trace_mul_left.mpr
    intro B
    have hB : B ∈ H := by rw [hfull]; trivial
    have hh : Matrix.trace (B*S) = 0 := by
      apply Submodule.span_induction (p := fun B _ => Matrix.trace (B*S) = 0)
        (fun B h => by obtain ⟨i,rfl⟩ := h; exact hz i)
        (by simp)
        (fun A B _ _ hA hB => by simp [Matrix.add_mul, Matrix.trace_add, hA, hB])
        (fun c A _ hA => by simp [Matrix.smul_mul, Matrix.trace_smul, hA]) hB
    simpa using hh
  let E := LinearMap.ker (scalarFunctional d w C)
  obtain ⟨hL,htrace,S,hS,hpattern⟩ := scalar_kernel_source d w C hell
  let Q : Finset (Fin (w.length+1)) := Finset.univ.filter
    (fun i => ∃ c : ℝ, acquisition (w.take i.val) = c • scalarRepresentative d w C)
  have hq : Q.card ≤ d+1 := cumulative_proportionality_card_even w (d+1) (by omega) hM _
  have zeroQ (T : E) (i : Fin (w.length+1)) (hi : i ∈ Q) :
      Matrix.trace (acquisition (w.take i.val)*T.val) = 0 := by
    obtain ⟨c,hc⟩ := (Finset.mem_filter.mp hi).2
    rw [hc, Matrix.smul_mul, Matrix.trace_smul, htrace]
    change c * scalarFunctional d w C T.val = 0
    rw [T.property, mul_zero]
  let U := {i : Fin (w.length+1) // i ∉ Q}
  let cut : History w →ₗ[ℝ] (U → ℝ) := LinearMap.pi (fun i => LinearMap.proj i.val)
  let obs : E →ₗ[ℝ] (U → ℝ) :=
    LinearMap.pi (fun i => (traceObservation (acquisition (w.take i.val.val))).comp E.subtype)
  have hinj : Function.Injective obs := by
    apply (injective_iff_map_eq_zero obs).mpr
    intro T hT
    apply Subtype.ext
    apply separates
    intro i
    by_cases hi : i ∈ Q
    · exact zeroQ T i hi
    · exact congrFun hT ⟨i,hi⟩
  let V := LinearMap.range obs
  have hE : Module.finrank ℝ E = 3 := by
    have hh := Module.Dual.finrank_ker_add_one_of_ne_zero hell
    change Module.finrank ℝ E + 1 = Module.finrank ℝ Mat at hh
    omega
  have hV : Module.finrank ℝ V = 3 := (LinearMap.finrank_range_of_inj hinj).trans hE
  let K0 : Submodule ℝ (History w) := {
    carrier := {v | v ∈ LinearMap.ker C.mulVecLin ∧ ∀ i ∈ Q, v i = 0}
    zero_mem' := by simp
    add_mem' := by
      rintro a b ⟨ha,hqa⟩ ⟨hb,hqb⟩
      exact ⟨(LinearMap.ker C.mulVecLin).add_mem ha hb, fun i hi => by simp [hqa i hi,hqb i hi]⟩
    smul_mem' := by
      rintro c a ⟨ha,hqa⟩
      exact ⟨(LinearMap.ker C.mulVecLin).smul_mem c ha, fun i hi => by simp [hqa i hi]⟩ }
  let K := K0.map cut
  have hk0 : K0 ≤ LinearMap.ker C.mulVecLin := fun _ h => h.1
  have hsurj := scalar_readout_surjective d w C _ hell he
  have hrC : Module.finrank ℝ (LinearMap.range C.mulVecLin) = d+1 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi]
    simp
  have hdim := C.mulVecLin.finrank_range_add_finrank_ker
  have htotal : Module.finrank ℝ (Fin (w.length+1) → ℝ) = w.length+1 := by simp
  have hkerdim : Module.finrank ℝ (LinearMap.ker C.mulVecLin) = d+2 := by
    rw [hrC,htotal] at hdim
    omega
  have hKdim : Module.finrank ℝ K ≤ d+2 :=
    (Submodule.finrank_map_le cut K0).trans ((Submodule.finrank_mono hk0).trans hkerdim.le)
  have hKstrict : Q.Nonempty → Module.finrank ℝ K ≤ d+1 := by
    rintro ⟨i,hi⟩
    have hlt : K0 < LinearMap.ker C.mulVecLin := by
      apply lt_of_le_of_ne hk0
      intro hh
      have hm : (fun _ : Fin (w.length+1) => (1 : ℝ)) ∈ K0 := by rw [hh]; exact hb
      have hz := hm.2 i hi
      norm_num at hz
    have hh := Submodule.finrank_lt_finrank_of_lt hlt
    have hmap := Submodule.finrank_map_le cut K0
    rw [hkerdim] at hh
    change Module.finrank ℝ K ≤ Module.finrank ℝ K0 at hmap
    omega
  let a : U → ℝ := obs ⟨S,hS⟩
  have ha : a ∈ V := ⟨⟨S,hS⟩,rfl⟩
  have hna : ∀ i, a i ≠ 0 := by
    intro i hz
    have hi := (hpattern i.val).mp hz
    exact i.property (by simp [Q,hi])
  let t : U → ℝ := fun i => (i.val.val : ℝ)
  have ht : Function.Injective t := by
    intro i j hij
    apply Subtype.ext
    apply Fin.ext
    change (i.val.val : ℝ) = (j.val.val : ℝ) at hij
    exact_mod_cast hij
  have hproducts : ∀ v ∈ V, ∀ j ≤ d, (fun i => v i * t i ^ j) ∈ K := by
    rintro _ ⟨T,rfl⟩ j hj
    let β : Coeff d := Pi.single ⟨j,by omega⟩ 1
    let z := (responseMatrix d w T.val).mulVec β
    have hz : z ∈ K0 := by
      constructor
      · exact response_range_le_kernel d w C _ he T.val T.property ⟨β,rfl⟩
      · intro i hi
        simp [z, β, Matrix.mulVec_single, responseMatrix, zeroQ T i hi]
    apply Submodule.mem_map.mpr
    refine ⟨z,hz,?_⟩
    ext i
    simp [cut, z, β, obs, traceObservation, responseMatrix, t, Matrix.mulVec_single]
  have hg := weighted_polynomial_span_growth t ht V K a ha hna d hproducts
  rw [hV] at hg
  have hcard : Fintype.card U + Q.card = w.length+1 := by
    have hh := Fintype.card_subtype_compl (fun i : Fin (w.length+1) => i ∈ Q)
    have hqcard : Fintype.card {i : Fin (w.length+1) // i ∈ Q} = Q.card := by simp
    change Fintype.card U = Fintype.card (Fin (w.length+1)) -
      Fintype.card {i : Fin (w.length+1) // i ∈ Q} at hh
    rw [Fintype.card_fin, hqcard] at hh
    have hle : Q.card ≤ w.length+1 := (Finset.card_le_card (Finset.subset_univ Q)).trans (by simp)
    omega
  by_cases hq0 : Q = ∅
  · simp only [hq0,Finset.card_empty] at hcard
    omega
  · have hstrict := hKstrict (Finset.nonempty_iff_ne_empty.mpr hq0)
    omega

#print axioms critical_scalar_span

end D5.S3.Observer.Linear.GainRay
