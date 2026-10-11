/- GID: D5/S3/Arith/Lattices/Klartag/Walk/Increments
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Walk/Increments
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian matrix walk, filtration and stopped increments. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail2

open D5.S3.Arith.Lattices.Klartag.Gaussian

namespace D5.S3.Arith.Lattices.Klartag.Walk.Increments

open MeasureTheory
open ProbabilityTheory
open Matrix
open Finset
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Rotational invariance.**  The standard Gaussian on a finite-dimensional real inner product
space is invariant under every linear isometry equivalence.  This is the one-line replacement for
the use of Lévy's characterisation in Klartag's Lemma 3.1. -/
theorem map_stdGaussian_isometry (U : E ≃ₗᵢ[ℝ] E) : (stdGaussian E).map U = stdGaussian E :=
  stdGaussian_map U

end Rotation

section Frozen

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {α : Type*} [MeasurableSpace α]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

end Frozen

section Projected

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [mE : MeasurableSpace E] [BorelSpace E]

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The characteristic function of a pushforward, when the map has an explicit "adjoint".  Stated
without `ContinuousLinearMap.adjoint` so that no `CompleteSpace` hypothesis is needed and the
formula can be used for maps into a different space. -/
theorem charFun_map_of_inner {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace F] [OpensMeasurableSpace F] (μ : Measure E) (L : E → F) (hL : Measurable L)
    (a : F → E)
    (h : ∀ x t, ⟪L x, t⟫ = ⟪x, a t⟫) (t : F) :
    charFun (μ.map L) t = charFun μ (a t) := by
  have hcont : Continuous fun y : F => Complex.exp ((⟪y, t⟫ : ℝ) * Complex.I) := by
    refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_ofReal.comp
      (continuous_inner.comp (continuous_id.prodMk continuous_const))
  rw [charFun_apply, charFun_apply,
    integral_map hL.aemeasurable hcont.aestronglyMeasurable]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [h x t])

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {α : Type*} [mα : MeasurableSpace α]

end Projected

section GOE

variable {n : ℕ}

/-- The upper triangle, including the diagonal: the index set of the coordinates of a symmetric
matrix. -/
abbrev UT (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

/-- The sorted pair `(min i j, max i j)`. -/
def up (i j : Fin n) : UT n := ⟨(min i j, max i j), min_le_max⟩

theorem up_comm (i j : Fin n) : up i j = up j i := by simp [up, min_comm, max_comm]

theorem up_of_le {i j : Fin n} (h : i ≤ j) : up i j = ⟨(i, j), h⟩ := by
  simp [up, min_eq_left h, max_eq_right h]

@[simp] theorem up_coe (p : UT n) : up p.1.1 p.1.2 = p := by rw [up_of_le p.2]

theorem up_eq_iff {a b c d : Fin n} (hab : a ≤ b) (hcd : c ≤ d) (h : up a b = up c d) :
    a = c ∧ b = d := by
  rw [up_of_le hab, up_of_le hcd] at h
  have h' := congrArg Subtype.val h
  simp only at h'
  exact ⟨congrArg Prod.fst h', congrArg Prod.snd h'⟩

/-- The coordinate weight: `1` on the diagonal, `1/√2` off it.  These are the coefficients that
make `symMat` a Frobenius isometry. -/
def cc (p : UT n) : ℝ := if p.1.1 = p.1.2 then 1 else (Real.sqrt 2)⁻¹

theorem cc_diag {p : UT n} (h : p.1.1 = p.1.2) : cc p = 1 := by simp [cc, h]

theorem cc_offdiag {p : UT n} (h : p.1.1 ≠ p.1.2) : cc p * cc p = 1 / 2 := by
  simp only [cc, if_neg h]
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- The symmetric matrix with the given Frobenius coordinates. -/
def symMat (x : EuclideanSpace ℝ (UT n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => cc (up i j) * x (up i j)

theorem symMat_apply (x : EuclideanSpace ℝ (UT n)) (i j : Fin n) :
    symMat x i j = cc (up i j) * x (up i j) := rfl

theorem symMat_isSymm (x : EuclideanSpace ℝ (UT n)) : (symMat x).IsSymm := by
  refine Matrix.IsSymm.ext fun i j => ?_
  rw [symMat_apply, symMat_apply, up_comm]

theorem symMat_swap (x : EuclideanSpace ℝ (UT n)) (i j : Fin n) :
    symMat x j i = symMat x i j := by rw [symMat_apply, symMat_apply, up_comm]

theorem symMat_apply_ut (x : EuclideanSpace ℝ (UT n)) (p : UT n) :
    symMat x p.1.1 p.1.2 = cc p * x p := by rw [symMat_apply, up_coe]

/-- The fibre of the sorting map over `p` is the (possibly degenerate) pair `{(a,b), (b,a)}`. -/
theorem fiber_up (p : UT n) :
    (Finset.univ.filter fun q : Fin n × Fin n => up q.1 q.2 = p)
      = {(p.1.1, p.1.2), (p.1.2, p.1.1)} := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro h
    rcases le_total q.1 q.2 with hq | hq
    · left
      rw [up_of_le hq] at h
      have h' := congrArg Subtype.val h
      simp only at h'
      exact Prod.ext (congrArg Prod.fst h') (congrArg Prod.snd h')
    · right
      rw [up_comm, up_of_le hq] at h
      have h' := congrArg Subtype.val h
      simp only at h'
      exact Prod.ext (congrArg Prod.snd h') (congrArg Prod.fst h')
  · rintro (rfl | rfl)
    · exact up_coe p
    · rw [up_comm]; exact up_coe p

/-- **`symMat` is a Frobenius isometry.**  This is what justifies modelling `R^{n×n}_sym` by
`EuclideanSpace ℝ (UT n)`: the Euclidean inner product of the coordinates is the Frobenius inner
product `∑_{i,j} A_ij B_ij` of the matrices. -/
theorem sum_symMat_mul (x y : EuclideanSpace ℝ (UT n)) :
    ∑ q : Fin n × Fin n, symMat x q.1 q.2 * symMat y q.1 q.2 = ∑ p : UT n, x p * y p := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun q : Fin n × Fin n => up q.1 q.2) (fun q _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [fiber_up p]
  rcases eq_or_ne p.1.1 p.1.2 with hd | hd
  · have h1 : ((p.1.2, p.1.1) : Fin n × Fin n) = (p.1.1, p.1.2) := by rw [hd]
    rw [h1, Finset.pair_eq_singleton, Finset.sum_singleton, symMat_apply_ut, symMat_apply_ut,
      cc_diag hd]
    ring
  · have h2 : ((p.1.1, p.1.2) : Fin n × Fin n) ≠ (p.1.2, p.1.1) := fun h => hd (congrArg Prod.fst h)
    rw [Finset.sum_pair h2, symMat_swap x p.1.1 p.1.2, symMat_swap y p.1.1 p.1.2,
      symMat_apply_ut, symMat_apply_ut]
    have hcc := cc_offdiag hd
    linear_combination (2 * x.ofLp p * y.ofLp p) * hcc

theorem sum_symMat_mul_eq_inner (x y : EuclideanSpace ℝ (UT n)) :
    ∑ i, ∑ j, symMat x i j * symMat y i j = ⟪x, y⟫ := by
  have h := sum_symMat_mul x y
  rw [Fintype.sum_prod_type] at h
  rw [h]
  simp [PiLp.inner_apply, mul_comm]

/-- The symmetric matrix with prescribed upper-triangular entries. -/
def mkMat (u : UT n → ℝ) : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => u (up i j)

/-- `mkMat` followed by `Matrix.toEuclideanCLM`, bundled as a linear map so that its continuity is
`LinearMap.continuous_of_finiteDimensional`. -/
def mkCLM (n : ℕ) :
    (UT n → ℝ) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) where
  toFun u := Matrix.toEuclideanCLM (𝕜 := ℝ) (mkMat u)
  map_add' u v := by
    have h : mkMat (u + v) = mkMat u + mkMat v := by ext i j; simp [mkMat]
    rw [h, map_add]
  map_smul' c u := by
    have h : mkMat (c • u) = c • mkMat u := by ext i j; simp [mkMat]
    rw [h, map_smul]; rfl

theorem measurable_opNorm_mkMat :
    Measurable fun u : UT n → ℝ => ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (mkMat u)‖ :=
  ((LinearMap.continuous_of_finiteDimensional (mkCLM n)).norm).measurable

/-- The Frobenius coordinates of the scaled symmetric Gaussian matrix. -/
def coordVec (r : ℝ) (x : EuclideanSpace ℝ (UT n)) : UT n → ℝ := fun p => r * cc p * x p

theorem measurable_coordVec (r : ℝ) : Measurable (coordVec (n := n) r) :=
  measurable_pi_iff.mpr fun p =>
    ((measurable_pi_apply p).comp (WithLp.measurable_ofLp _ _)).const_mul _

theorem smul_symMat_eq_mkMat (r : ℝ) (x : EuclideanSpace ℝ (UT n)) :
    r • symMat x = mkMat (coordVec r x) := by
  ext i j
  simp only [Matrix.smul_apply, symMat_apply, mkMat, Matrix.of_apply, coordVec, smul_eq_mul]
  ring

/-- The auxiliary probability space carrying a matrix with i.i.d. entries: a product indexed by the
upper triangle and then by the two independent slots `B a b` and `B b a`. -/
abbrev Aux (n : ℕ) := UT n → Fin 2 → ℝ

def auxMeasure (n : ℕ) (v : ℝ≥0) : Measure (Aux n) :=
  Measure.pi fun _ : UT n => Measure.pi fun _ : Fin 2 => gaussianReal 0 v

instance (n : ℕ) (v : ℝ≥0) : IsProbabilityMeasure (auxMeasure n v) := by
  unfold auxMeasure; infer_instance

/-- The matrix with i.i.d. entries. -/
def auxB (ω : Aux n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ω (up i j) (if i ≤ j then 0 else 1)

/-- The index map `(i,j) ↦ (sorted pair, slot)`; it is injective, which is why the entries of
`auxB` are independent over the full product. -/
def eIdx (q : Fin n × Fin n) : UT n × Fin 2 := (up q.1 q.2, if q.1 ≤ q.2 then 0 else 1)

theorem eIdx_injective : Function.Injective (eIdx (n := n)) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  simp only [eIdx, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  by_cases hij : i ≤ j <;> by_cases hkl : k ≤ l
  · obtain ⟨e1, e2⟩ := up_eq_iff hij hkl h1
    simp [e1, e2]
  · simp [hij, hkl] at h2
  · simp [hij, hkl] at h2
  · rw [up_comm i j, up_comm k l] at h1
    obtain ⟨e1, e2⟩ := up_eq_iff (le_of_not_ge hij) (le_of_not_ge hkl) h1
    simp [e1, e2]

theorem aux_meas (p : UT n) (k : Fin 2) : Measurable fun ω : Aux n => ω p k :=
  (measurable_pi_apply k).comp (measurable_pi_apply p)

theorem aux_eval (v : ℝ≥0) (p : UT n) :
    (auxMeasure n v).map (fun ω : Aux n => ω p) = Measure.pi fun _ : Fin 2 => gaussianReal 0 v :=
  (measurePreserving_eval _ p).map_eq

theorem aux_eval2 (v : ℝ≥0) (p : UT n) (k : Fin 2) :
    (auxMeasure n v).map (fun ω : Aux n => ω p k) = gaussianReal 0 v := by
  have h : (fun ω : Aux n => ω p k) = (fun z : Fin 2 → ℝ => z k) ∘ (fun ω : Aux n => ω p) := rfl
  rw [h, ← Measure.map_map (by fun_prop) (by fun_prop), aux_eval,
    (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 v) k).map_eq]

theorem aux_inner_indep (v : ℝ≥0) (p : UT n) :
    iIndepFun (fun (k : Fin 2) (ω : Aux n) => ω p k) (auxMeasure n v) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (fun k => (aux_meas p k).aemeasurable)]
  rw [show (fun (ω : Aux n) (k : Fin 2) => ω p k) = (fun ω : Aux n => ω p) from rfl, aux_eval]
  congr 1
  funext k
  rw [aux_eval2]

theorem aux_coord_indep (v : ℝ≥0) :
    iIndepFun (fun (q : UT n × Fin 2) (ω : Aux n) => ω q.1 q.2) (auxMeasure n v) := by
  refine iIndepFun_uncurry' (fun i j => aux_meas i j) ?_ (aux_inner_indep v)
  exact iIndepFun_pi (X := fun _ : UT n => (id : (Fin 2 → ℝ) → (Fin 2 → ℝ)))
    (fun _ => aemeasurable_id)

/-- **The first hypothesis `D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail` consumes**: the entries of `auxB` are
independent over the full product `Fin n × Fin n`. -/
theorem auxB_indep (v : ℝ≥0) :
    iIndepFun (fun (q : Fin n × Fin n) (ω : Aux n) => auxB ω q.1 q.2) (auxMeasure n v) :=
  (aux_coord_indep (n := n) v).precomp (eIdx_injective (n := n))

/-- **The second hypothesis `D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail` consumes**: every entry of `auxB` is
`N(0, v)`. -/
theorem auxB_law (v : ℝ≥0) (i j : Fin n) :
    (auxMeasure n v).map (fun ω : Aux n => auxB ω i j) = gaussianReal 0 v :=
  aux_eval2 v _ _

/-- The block map producing the symmetrised entry from the two independent slots. -/
def phi (p : UT n) (z : Fin 2 → ℝ) : ℝ := if p.1.1 = p.1.2 then 2 * z 0 else z 0 + z 1

theorem measurable_phi (p : UT n) : Measurable (phi p) := by
  unfold phi; split
  · exact (measurable_pi_apply 0).const_mul 2
  · exact (measurable_pi_apply 0).add (measurable_pi_apply 1)

theorem phi_diag {p : UT n} (h : p.1.1 = p.1.2) : phi p = fun z : Fin 2 → ℝ => 2 * z 0 := by
  funext z; simp [phi, h]

theorem phi_offdiag {p : UT n} (h : p.1.1 ≠ p.1.2) :
    phi p = fun z : Fin 2 → ℝ => z 0 + z 1 := by
  funext z; simp [phi, h]

theorem auxV_eq (ω : Aux n) (p : UT n) :
    auxB ω p.1.1 p.1.2 + auxB ω p.1.2 p.1.1 = phi p (ω p) := by
  have h1 : auxB ω p.1.1 p.1.2 = ω p 0 := by
    simp only [auxB, Matrix.of_apply, up_coe, if_pos p.2]
  have h2 : auxB ω p.1.2 p.1.1 = ω p (if p.1.2 ≤ p.1.1 then 0 else 1) := by
    simp only [auxB, Matrix.of_apply, up_comm p.1.2 p.1.1, up_coe]
  rw [h1, h2]
  unfold phi
  by_cases hd : p.1.1 = p.1.2
  · rw [if_pos hd, if_pos (le_of_eq hd.symm)]; ring
  · rw [if_neg hd, if_neg (fun h => hd (le_antisymm p.2 h))]

theorem auxB_add_transpose (ω : Aux n) :
    auxB ω + (auxB ω)ᵀ = mkMat (fun p => phi p (ω p)) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.transpose_apply, mkMat, Matrix.of_apply]
  rw [← auxV_eq ω (up i j)]
  rcases le_total i j with h | h
  · rw [up_of_le h]
  · rw [up_comm, up_of_le h]; ring

/-- `v = r²/4`: the entry variance of the i.i.d. matrix that matches the scaling `r` of the
symmetric Gaussian. -/
def vOf (r : ℝ) : ℝ≥0 := Real.toNNReal (r ^ 2 / 4)

/-- The variance of the symmetrised entry at `p`: `r²` on the diagonal, `r²/2` off it — Klartag's
`E Γ_ij ^ 2 = (1 + δ_ij)/n` after the scaling `r = √(2/n)`. -/
def varOf (r : ℝ) (p : UT n) : ℝ≥0 := Real.toNNReal ((r * cc p) ^ 2)

theorem coe_vOf (r : ℝ) : ((vOf r : ℝ≥0) : ℝ) = r ^ 2 / 4 :=
  Real.coe_toNNReal _ (by positivity)

theorem coe_varOf (r : ℝ) (p : UT n) : ((varOf r p : ℝ≥0) : ℝ) = (r * cc p) ^ 2 :=
  Real.coe_toNNReal _ (sq_nonneg _)

theorem map_phi (r : ℝ) (p : UT n) :
    (Measure.pi fun _ : Fin 2 => gaussianReal 0 (vOf r)).map (phi p)
      = gaussianReal 0 (varOf r p) := by
  classical
  set Q : Measure (Fin 2 → ℝ) := Measure.pi fun _ : Fin 2 => gaussianReal 0 (vOf r) with hQ
  have hev : ∀ k : Fin 2, HasLaw (fun z : Fin 2 → ℝ => z k) (gaussianReal 0 (vOf r)) Q :=
    fun k => (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 (vOf r)) k).hasLaw
  by_cases hd : p.1.1 = p.1.2
  · rw [phi_diag hd]
    have h : (fun z : Fin 2 → ℝ => 2 * z 0) = ((2 : ℝ) * ·) ∘ (fun z : Fin 2 → ℝ => z 0) := rfl
    rw [h, ← Measure.map_map (by fun_prop : Measurable fun x : ℝ => 2 * x)
      (measurable_pi_apply (0 : Fin 2)), (hev 0).map_eq, gaussianReal_map_const_mul]
    refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_mul, coe_vOf, coe_varOf, cc_diag hd]
    simp
    ring
  · rw [phi_offdiag hd]
    have hind : IndepFun (fun z : Fin 2 → ℝ => z 0) (fun z : Fin 2 → ℝ => z 1) Q := by
      have hpi := iIndepFun_pi (X := fun _ : Fin 2 => (id : ℝ → ℝ))
        (μ := fun _ : Fin 2 => gaussianReal 0 (vOf r)) (fun _ => aemeasurable_id)
      exact hpi.indepFun (by decide)
    have hsum := gaussianReal_add_gaussianReal_of_indepFun hind (hev 0) (hev 1)
    rw [show (fun z : Fin 2 → ℝ => z 0 + z 1)
        = (fun z : Fin 2 → ℝ => z 0) + (fun z : Fin 2 → ℝ => z 1) from rfl, hsum]
    refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
    refine NNReal.coe_injective ?_
    rw [NNReal.coe_add, coe_vOf, coe_varOf]
    have hcc := cc_offdiag hd
    linear_combination (-(r ^ 2)) * hcc

theorem map_auxV (r : ℝ) :
    (auxMeasure n (vOf r)).map (fun ω : Aux n => fun p => phi p (ω p))
      = Measure.pi fun p : UT n => gaussianReal 0 (varOf r p) := by
  have hsf : ∀ p : UT n,
      SigmaFinite ((Measure.pi fun _ : Fin 2 => gaussianReal 0 (vOf r)).map (phi p)) := by
    intro p; rw [map_phi]; infer_instance
  rw [auxMeasure, Measure.pi_map_pi (fun p => (measurable_phi p).aemeasurable)]
  congr 1
  funext p
  exact map_phi r p

theorem map_ofLp_stdGaussian :
    (stdGaussian (EuclideanSpace ℝ (UT n))).map WithLp.ofLp
      = Measure.pi fun _ : UT n => gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian (ι := UT n), Measure.map_map (by fun_prop) (by fun_prop),
    show (WithLp.ofLp ∘ (WithLp.toLp 2 : (UT n → ℝ) → EuclideanSpace ℝ (UT n))) = id from rfl,
    Measure.map_id]

theorem map_coordVec {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (r : ℝ)
    {ξ : Ω → EuclideanSpace ℝ (UT n)} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ (UT n))) :
    P.map (fun ω => coordVec r (ξ ω)) = Measure.pi fun p : UT n => gaussianReal 0 (varOf r p) := by
  have hstep : (fun ω => coordVec r (ξ ω))
      = ((fun u : UT n → ℝ => fun p => (r * cc p) * u p) ∘ WithLp.ofLp) ∘ ξ := by
    funext ω p; simp only [coordVec, Function.comp_apply]
  have hmeas : Measurable fun u : UT n → ℝ => fun p : UT n => (r * cc p) * u p :=
    measurable_pi_iff.mpr fun p => (measurable_pi_apply p).const_mul _
  rw [hstep, ← Measure.map_map (hmeas.comp (WithLp.measurable_ofLp _ _)) hξ, hlaw,
    ← Measure.map_map hmeas (WithLp.measurable_ofLp _ _), map_ofLp_stdGaussian,
    Measure.pi_map_pi (fun p => (measurable_const_mul (r * cc p)).aemeasurable)]
  congr 1
  funext p
  rw [show (fun u : ℝ => (r * cc p) * u) = ((r * cc p) * ·) from rfl, gaussianReal_map_const_mul]
  refine gaussianReal_ext_iff.2 ⟨by ring, ?_⟩
  refine NNReal.coe_injective ?_
  rw [NNReal.coe_mul, coe_varOf]
  simp

/-- **The law of the symmetric Gaussian matrix is the law of `B + Bᵀ` with i.i.d. `B`.**  This is
Lemma 3.1's output in discrete form: it is what lets `D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail`, whose matrix is
`B + Bᵀ` with independent entries over the full product, be applied to the chain's increment, whose
entries above and below the diagonal are *equal* and therefore not independent. -/
theorem map_coordVec_eq_map_auxV {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (r : ℝ)
    {ξ : Ω → EuclideanSpace ℝ (UT n)} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ (UT n))) :
    P.map (fun ω => coordVec r (ξ ω))
      = (auxMeasure n (vOf r)).map (fun ω : Aux n => fun p => phi p (ω p)) := by
  rw [map_coordVec r hξ hlaw, map_auxV]

theorem measureReal_preimage {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A)
    {f : A → B} (hf : Measurable f) {S : Set B} (hS : MeasurableSet S) :
    μ.real (f ⁻¹' S) = (μ.map f).real S := by
  rw [measureReal_def, measureReal_def, Measure.map_apply hf hS]

theorem sqrt_coe_vOf {r : ℝ} (hr : 0 ≤ r) : Real.sqrt ((vOf r : ℝ≥0) : ℝ) = r / 2 := by
  rw [coe_vOf, show r ^ 2 / 4 = (r / 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]

theorem vOf_pos {r : ℝ} (hr : 0 < r) : 0 < vOf r :=
  Real.toNNReal_pos.2 (by positivity)

/-- **Klartag, Corollary 3.2, for the discrete chain's increment.**  If `ξ` is a standard Gaussian
on the model `EuclideanSpace ℝ (UT n)` of `R^{n×n}_sym`, then the symmetric matrix `r · symMat ξ`
— which is the increment of the Dyson walk after time `r²`, `E (W_t)_ij² = t (1 + δ_ij)/2` —
satisfies, for every `s ≥ 1`,

`P(‖r · symMat ξ‖_op ≥ 6 r s √n) ≤ 4 exp (-s² n)`.

The proof runs `D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail` on the auxiliary i.i.d. space and transports the
conclusion along `map_coordVec_eq_map_auxV`. -/
theorem increment_opNorm_tail {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {r : ℝ} (hr : 0 < r)
    {ξ : Ω → EuclideanSpace ℝ (UT n)} (hξ : Measurable ξ)
    (hlaw : P.map ξ = stdGaussian (EuclideanSpace ℝ (UT n))) (s : ℝ) (hs : 1 ≤ s) :
    P.real {ω | 6 * r * s * Real.sqrt n ≤
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • symMat (ξ ω))‖} ≤ 4 * Real.exp (-(s ^ 2 * n)) := by
  classical
  set thr : ℝ := 6 * r * s * Real.sqrt n with hthr
  set S : Set (UT n → ℝ) :=
    {u | thr ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (mkMat u)‖} with hS
  have hSmeas : MeasurableSet S := measurableSet_le measurable_const measurable_opNorm_mkMat
  have hset : {ω | thr ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • symMat (ξ ω))‖}
      = (fun ω => coordVec r (ξ ω)) ⁻¹' S := by
    ext ω; simp only [hS, Set.mem_ofPred_eq, Set.mem_preimage, smul_symMat_eq_mkMat]
  have hmeas : Measurable fun ω => coordVec r (ξ ω) := (measurable_coordVec r).comp hξ
  have hauxmeas : Measurable fun ω : Aux n => fun p => phi p (ω p) :=
    measurable_pi_iff.mpr fun p => (measurable_phi p).comp (measurable_pi_apply p)
  have hstep : P.real {ω | thr ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (r • symMat (ξ ω))‖}
      = (auxMeasure n (vOf r)).real ((fun ω : Aux n => fun p => phi p (ω p)) ⁻¹' S) := by
    rw [hset, measureReal_preimage P hmeas hSmeas, map_coordVec_eq_map_auxV r hξ hlaw,
      ← measureReal_preimage _ hauxmeas hSmeas]
  have hset2 : ((fun ω : Aux n => fun p => phi p (ω p)) ⁻¹' S)
      = {ω : Aux n | 12 * Real.sqrt ((vOf r : ℝ≥0) : ℝ) * s * Real.sqrt n ≤
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (auxB ω + (auxB ω)ᵀ)‖} := by
    ext ω
    simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, auxB_add_transpose ω]
    rw [sqrt_coe_vOf hr.le, hthr]
    constructor <;> intro h <;> linarith [h]
  rw [hstep, hset2]
  exact D5.S3.Arith.Lattices.Klartag.Gaussian.GOETail.gaussian_opNormTail (auxMeasure n (vOf r)) n auxB (vOf r) (vOf_pos hr)
    (auxB_indep _) (auxB_law _) s hs

end GOE

end

end D5.S3.Arith.Lattices.Klartag.Walk.Increments
