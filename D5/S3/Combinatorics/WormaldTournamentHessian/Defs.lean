/- GID: D5/S3/Combinatorics/WormaldTournamentHessian/Defs
   generality: G
   mirror-B: D5/B/S3/Combinatorics/WormaldTournamentHessian/Defs
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv, mathlib/module/Mathlib.Analysis.Calculus.ContDiff.RestrictScalars, mathlib/module/Mathlib.Analysis.Matrix.Normed]
   utility: none
   digest: Tournament definitions and logarithmic second variation. -/

/-
admission_basis: escape-witness
Utility is none: arbitrary finite-dimensional identities and complex C2 local
solutions, not finite certificates. Direct frozen D5 dependencies: none.
Live content: WormaldAnalytic.logarithmicPhase_second and WormaldAnalytic.actual_hessian.
Judgments use the bypass test; binding and normalization do not create content.

name | proof_shape | escape_witness | consumers | frozen deps
IsRegularTournament | bind-only (definition) | none | claim | frozen deps: none
  Definition of the source hypothesis; no proved assertion or escape witness.
adjacency | bind-only (definition) | none | skewAdjacency, K | frozen deps: none
  Boolean-to-integral coordinate encoding; no proved assertion.
skewAdjacency | bind-only (definition) | none | skewDiag, skewNormLe | frozen deps: none
  Auxiliary subtraction and transpose definition; no proved assertion.
z | bind-only (definition) | none | IsLocalSolution, phase | frozen deps: none
  Source expansion-point definition; no proved assertion.
K | bind-only (definition) | none | IsLocalSolution, polynomialSmooth | frozen deps: none
  Source determinant-polynomial definition; no proved assertion.
appendLast | bind-only (definition) | none | IsLocalSolution, appendLastLinearApply | frozen deps: none
  Coordinate-assembly definition; no proved assertion.
IsLocalSolution | bind-only (definition) | none | claim | frozen deps: none
  Value, complex C2 and local-equation predicate; no proved assertion.
phase | bind-only (definition) | none | hessian | frozen deps: none
  Source phase encoded with the principal complex logarithm; no proved assertion.
hessian | bind-only (definition) | none | calH, WormaldAnalytic.actual_hessian | frozen deps: none
  Source angular Hessian encoded by two real derivatives; no proved assertion.
calH | bind-only (definition) | none | claim, result | frozen deps: none
  Source Hessian determinant definition; no proved assertion.
claim | bind-only (definition) | none | result | frozen deps: none
  Quantified target definition, unfolded by result; no proved assertion.
regularDegree | bind-only | none | regularOdd, determinantAtBase, regularColumnSlopeValue, regularSkewRowSum | frozen deps: none
  Sum the orientation identity and the given constant row sums; all remaining facts are finite-sum and integer normalization.
regularOdd | bind-only | none | regularAlgebraicSquare, calH_closedForm | frozen deps: none
  Existential projection from regularDegree, which itself has only normalization content.
determinantAtBase | bind-only | none | localSolutionOfInvertible, regularColumnSlopeValue | frozen deps: none
  Normalize the constant-vector kernel identity and apply the existing determinant-zero theorem.
WormaldAnalytic.second | bind-only (definition) | none | WormaldAnalytic.second_comp | frozen deps: none
  Directional second-derivative notation; no proved assertion.
WormaldAnalytic.second_comp | bind-only | none | WormaldAnalytic.implicit_second_graph, WormaldAnalytic.second_comp_clm, WormaldAnalytic.second_angular_substitution, WormaldAnalytic.logarithmicPhase_second | frozen deps: none
  Instantiate the existing first-derivative composition and continuous-linear evaluation rules twice; normalize their presentations.
WormaldAnalytic.second_eq_zero_of_eventually | bind-only | none | WormaldAnalytic.implicit_second_graph | frozen deps: none
  Apply existing germ equality rules for fderiv twice and the derivative of a constant.
WormaldAnalytic.second_graph | bind-only | none | WormaldAnalytic.implicit_second_graph | frozen deps: none
  Instantiate product and identity derivative rules twice; the first graph component normalizes to zero.
WormaldAnalytic.implicit_first_graph | bind-only | none | WormaldAnalytic.implicit_first_scalar | frozen deps: none
  Apply the chain rule to the zero graph germ and project to a direction.
WormaldAnalytic.implicit_second_graph | bind-only | none | WormaldAnalytic.implicit_second_scalar | frozen deps: none
  Instantiate second_comp on the graph and use its zero germ; no new source-specific analytic relation.
WormaldAnalytic.implicit_first_scalar | bind-only | none | WormaldAnalytic.hessian_of_implicit_scalar | frozen deps: none
  Solve the scalar linear relation supplied by implicit_first_graph; normalization.
WormaldAnalytic.implicit_second_scalar | bind-only | none | WormaldAnalytic.hessian_of_implicit_scalar | frozen deps: none
  Solve the scalar linear relation supplied by implicit_second_graph; normalization.
WormaldAnalytic.second_sub_const | bind-only | none | WormaldAnalytic.hessian_of_implicit_scalar | frozen deps: none
  Direct fderiv_sub_const rewriting twice.
WormaldAnalytic.second_comp_clm | bind-only | none | WormaldAnalytic.hessian_of_implicit_scalar | frozen deps: none
  Specialize the existing chain-rule presentation to a linear map and normalize its zero second derivative.
WormaldAnalytic.second_eq_derivative | bind-only | none | WormaldAnalytic.second_sub_sub, WormaldAnalytic.second_complex_to_real, WormaldAnalytic.second_angular_substitution, WormaldAnalytic.logarithmicPhase_second | frozen deps: none
  Existing continuous-linear evaluation derivative identifies the two second-derivative presentations.
WormaldAnalytic.second_sub_sub | bind-only | none | WormaldAnalytic.hessian_of_implicit_coordinates | frozen deps: none
  Apply linearity in the two arguments of the derivative and normalize subtraction.
WormaldAnalytic.second_complex_to_real | bind-only | none | WormaldAnalytic.second_angular_substitution | frozen deps: none
  Direct order-two specialization of ContDiffAt.restrictScalars_iteratedFDeriv, normalized by iteratedFDeriv_two_apply and linear evaluation.
WormaldAnalytic.angularMap | bind-only (definition) | none | WormaldAnalytic.second_angular_substitution | frozen deps: none
  Real-linear imaginary-coordinate map definition; no proved assertion.
WormaldAnalytic.second_angular_substitution | bind-only | none | WormaldAnalytic.actual_hessian | frozen deps: none
  Restrict scalars using the consumed upstream specialization and normalize the two factors of I.
WormaldAnalytic.logarithmicPhase | bind-only (definition) | none | WormaldAnalytic.logarithmicPhase_smooth, WormaldAnalytic.logarithmicPhase_second | frozen deps: none
  Auxiliary logarithmic-chart phase definition; no proved assertion.
WormaldAnalytic.logarithmicPhase_smooth | bind-only | none | WormaldAnalytic.actual_hessian | frozen deps: none
  Instantiate complex log smoothness on the slit plane and smooth composition.
WormaldAnalytic.exponentialChart | bind-only (definition) | none | WormaldAnalytic.fderiv_exponentialChart, WormaldAnalytic.second_exponentialChart | frozen deps: none
  Auxiliary coordinatewise exponential chart definition; no proved assertion.
WormaldAnalytic.fderiv_exponentialChart | bind-only | none | WormaldAnalytic.second_exponentialChart, WormaldAnalytic.logarithmicPhase_second | frozen deps: none
  Instantiate the Pi, exponential and scalar-product derivative rules.
WormaldAnalytic.second_exponentialChart | bind-only | none | WormaldAnalytic.logarithmicPhase_second | frozen deps: none
  Apply the same exponential derivative rules to fderiv_exponentialChart and normalize at zero.
WormaldAnalytic.second_clog | bind-only | none | WormaldAnalytic.logarithmicPhase_second | frozen deps: none
  Instantiate the principal-log derivative on its open slit-plane germ, inverse and product rules; normalize the second presentation.
WormaldAnalytic.logarithmicPhase_second | content | WormaldAnalytic.logarithmicPhase_second: coupled log/chart second-variation relation, used by actual_hessian | WormaldAnalytic.actual_hessian | frozen deps: none
  Own step: the coupled log/exponential coordinate computation gives the diagonal correction minus the product of first derivatives. Its live second-variation relation is not a definition of the phase or a renamed upstream conclusion; no bypass using only the supplied first-order data is used.
WormaldAnalytic.actual_hessian | content | WormaldAnalytic.logarithmicPhase_second: live log/chart second-variation identity | WormaldAnalytic.hessian_of_implicit_scalar | frozen deps: none
  Propagation: the computed logarithmicPhase_second relation survives the scalar-restriction/angular substitution. The real angular Hessian is not definitionally the complex h-Hessian, and the proof consumes the mixed log/chart correction.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Matrix.Normed

/-! # Regular tournament Hessians: defs -/

public section

open scoped Topology ContDiff Matrix Matrix.Norms.Operator
open Matrix Filter


namespace D5.S3.Combinatorics.WormaldTournamentHessian.Defs

/-- An irreflexive orientation of every pair, with constant out-degree. -/
@[expose]
def IsRegularTournament {d : ℕ} (A : Fin d → Fin d → Bool) : Prop :=
  (∀ i, A i i = false) ∧
  (∀ i j, i ≠ j → (A i j = true ↔ A j i = false)) ∧
  ∃ r : ℕ, ∀ i, ∑ j, (if A i j then 1 else 0) = r

/-- The integral adjacency matrix. -/
@[expose]
def adjacency {d : ℕ} (A : Fin d → Fin d → Bool) : Matrix (Fin d) (Fin d) ℤ :=
  fun i j => if A i j then 1 else 0

/-- The integral skew adjacency matrix. -/
@[expose]
def skewAdjacency {d : ℕ} (A : Fin d → Fin d → Bool) : Matrix (Fin d) (Fin d) ℤ :=
  adjacency A - (adjacency A).transpose

/-- The point at which the implicit equation is expanded. -/
@[expose]
noncomputable def z (d : ℕ) : ℂ := 2 / d

/-- The determinant polynomial in the paper. -/
@[expose]
noncomputable def K {d : ℕ} (A : Fin d → Fin d → Bool) (y : Fin d → ℂ) : ℂ :=
  (1 - ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
    (adjacency A).map (Int.castRingHom ℂ)) * diagonal y).det

/-- Append the last coordinate, retaining the paper's vertex order. -/
@[expose]
def appendLast {d : ℕ} (y : Fin (d - 1) → ℂ) (t : ℂ) : Fin d → ℂ :=
  fun i => @Fin.snoc (d - 1) (fun _ => ℂ) y t
    (Fin.ofNat (d - 1 + 1) i.val)

/-- The local solution has the stated value, complex C² regularity and equation germ. -/
@[expose]
def IsLocalSolution {d : ℕ} (A : Fin d → Fin d → Bool)
    (h : (Fin (d - 1) → ℂ) → ℂ) : Prop :=
  h (fun _ => z d) = z d ∧
  ContDiffAt ℂ 2 h (fun _ => z d) ∧
  ∀ᶠ y in 𝓝 (fun _ : Fin (d - 1) => z d), K A (appendLast y (h y)) = 0

/-- The complex-valued phase function on real angular coordinates. -/
@[expose]
noncomputable def phase {d : ℕ} (h : (Fin (d - 1) → ℂ) → ℂ)
    (θ : Fin (d - 1) → ℝ) : ℂ :=
  Complex.log (h (fun j => z d * Complex.exp (Complex.I * θ j)))

/-- Second real Fréchet derivatives, evaluated in the two coordinate directions. -/
@[expose]
noncomputable def hessian {d : ℕ} (h : (Fin (d - 1) → ℂ) → ℂ) :
    Matrix (Fin (d - 1)) (Fin (d - 1)) ℂ :=
  fun j k => fderiv ℝ (fun θ => fderiv ℝ (phase h) θ (Pi.single j 1)) 0 (Pi.single k 1)

/-- Wormald's Hessian determinant. -/
@[expose]
noncomputable def calH {d : ℕ} (h : (Fin (d - 1) → ℂ) → ℂ) : ℂ :=
  (hessian h).det

/-- Conjecture 6, including existence and independence of the local solution. -/
@[expose]
def claim : Prop :=
  ∀ (d : ℕ), 3 ≤ d → ∀ A : Fin d → Fin d → Bool, IsRegularTournament A →
    (∃ h, IsLocalSolution A h) ∧
    ∀ h, IsLocalSolution A h → calH h ≠ 0 ∧ ∃ q : ℚ, (d : ℂ) / calH h = (q : ℂ) ^ 2

theorem regularDegree {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) : ∃ r : ℕ, d = 2 * r + 1 ∧ ∀ i, ∑ j, adjacency A i j = (r : ℤ) := by
  obtain ⟨hdiag, hdir, r, hr⟩ := hA
  have hpair : ∀ i j, adjacency A i j + adjacency A j i =
      (if i = j then 0 else 1 : ℤ) := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [adjacency, hdiag]
    · have h := hdir i j hij
      cases hai : A i j <;> cases haj : A j i <;> simp_all [adjacency]
  have hrow : ∀ i, ∑ j, adjacency A i j = (r : ℤ) := by
    intro i
    have h := hr i
    simp only [adjacency]
    exact_mod_cast h
  have hswap : (∑ i : Fin d, ∑ j : Fin d, adjacency A j i) =
      (∑ i : Fin d, ∑ j : Fin d, adjacency A i j) := Finset.sum_comm
  have hpairsum : ∀ i : Fin d, (∑ j : Fin d, (if i = j then 0 else 1 : ℤ)) = d - 1 := by
    intro i
    calc
      _ = ∑ j : Fin d, (1 - (if i = j then 1 else 0) : ℤ) := by
        apply Finset.sum_congr rfl
        intro j _
        split <;> simp_all
      _ = _ := by simp [Finset.sum_sub_distrib]
  have hcount : (d : ℤ) * (2 * r) = d * (d - 1) := by
    calc
      (d : ℤ) * (2 * r) =
          (∑ i : Fin d, ∑ j : Fin d, adjacency A i j) +
            (∑ i : Fin d, ∑ j : Fin d, adjacency A j i) := by
              rw [hswap]
              simp_rw [hrow]
              simp
              ring
      _ = ∑ i : Fin d, ∑ j : Fin d, (adjacency A i j + adjacency A j i) := by
        simp only [Finset.sum_add_distrib]
      _ = ∑ i : Fin d, ∑ j : Fin d, (if i = j then 0 else 1 : ℤ) := by simp_rw [hpair]
      _ = d * (d - 1) := by simp_rw [hpairsum]; simp; ring
  have heq : (d : ℤ) = 2 * r + 1 := by
    have hpos : (0 : ℤ) < d := by omega
    nlinarith
  refine ⟨r, ?_, hrow⟩
  exact_mod_cast heq


theorem regularOdd {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) : Odd d := by
  obtain ⟨r, hdr, _⟩ := regularDegree A hd hA
  exact ⟨r, hdr⟩

theorem determinantAtBase {d : ℕ} (A : Fin d → Fin d → Bool)
    (hd : 3 ≤ d) (hA : IsRegularTournament A) : K A (fun _ => z d) = 0 := by
  obtain ⟨r, hdr, hr⟩ := regularDegree A hd hA
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
  have hrow : ∀ i, ∑ j, ((adjacency A i j : ℤ) : ℂ) = r := by
    intro i
    exact_mod_cast hr i
  have hker : (1 - ((1 / 2 : ℂ) • (1 : Matrix (Fin d) (Fin d) ℂ) +
      (adjacency A).map (Int.castRingHom ℂ)) * diagonal (fun _ => z d)) *ᵥ
        (fun _ => (1 : ℂ)) = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.mul_diagonal,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, mul_one,
      Finset.sum_sub_distrib, ← Finset.sum_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, Matrix.map_apply, Pi.zero_apply]
    have hrow' : (∑ j, (Int.castRingHom ℂ) (adjacency A i j)) = (r : ℂ) := hrow i
    simp only [hrow']
    simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    unfold z
    have hdc : (d : ℂ) = 2 * r + 1 := by exact_mod_cast hdr
    field_simp
    linear_combination hdc
  exact Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hker
    (i := ⟨0, by omega⟩) (by simp)

namespace WormaldAnalytic

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

@[expose]
noncomputable def second (f : E → F) (x v w : E) : F :=
  fderiv 𝕜 (fun y => fderiv 𝕜 f y v) x w

private theorem second_comp (f : E → F) (g : F → G) (x v w : E)
    (hf : ContDiffAt 𝕜 2 f x) (hg : ContDiffAt 𝕜 2 g (f x)) :
    second (𝕜 := 𝕜) (g ∘ f) x v w =
      second (𝕜 := 𝕜) g (f x) (fderiv 𝕜 f x v) (fderiv 𝕜 f x w) +
      fderiv 𝕜 g (f x) (second (𝕜 := 𝕜) f x v w) := by
  have hf₁ := hf.differentiableAt (by norm_num)
  have hg₁ := hg.differentiableAt (by norm_num)
  have hf₂ : DifferentiableAt 𝕜 (fderiv 𝕜 f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hg₂ : DifferentiableAt 𝕜 (fderiv 𝕜 g) (f x) :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have heq : (fun y => fderiv 𝕜 (g ∘ f) y v) =ᶠ[𝓝 x]
      (fun y => fderiv 𝕜 g (f y) (fderiv 𝕜 f y v)) := by
    filter_upwards [hf.eventually (by norm_num),
      hf₁.continuousAt (hg.eventually (by norm_num))] with y hyf hyg
    have hyg' : ContDiffAt 𝕜 2 g (f y) := hyg
    rw [fderiv_comp y (hyg'.differentiableAt (by norm_num))
      (hyf.differentiableAt (by norm_num))]
    rfl
  unfold second
  rw [heq.fderiv_eq]
  have hc : DifferentiableAt 𝕜 (fun y => fderiv 𝕜 g (f y)) x := hg₂.comp x hf₁
  have hu : DifferentiableAt 𝕜 (fun y => fderiv 𝕜 f y v) x :=
    hf₂.clm_apply (differentiableAt_const v)
  rw [fderiv_clm_apply hc hu]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply]
  have hgapp : fderiv 𝕜 (fun y => fderiv 𝕜 g y (fderiv 𝕜 f x v)) (f x) =
      (fderiv 𝕜 (fderiv 𝕜 g) (f x)).flip (fderiv 𝕜 f x v) := by
    rw [fderiv_clm_apply hg₂ (differentiableAt_const (fderiv 𝕜 f x v))]
    simp
  rw [hgapp]
  rw [fderiv_fun_comp x hg₂ hf₁]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  abel

private theorem second_eq_zero_of_eventually {f : E → F} {x : E}
    (hf : f =ᶠ[𝓝 x] fun _ => 0) (v w : E) : second (𝕜 := 𝕜) f x v w = 0 := by
  have he : (fun y => fderiv 𝕜 f y v) =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hf.fderiv (𝕜 := 𝕜)] with y hy
    rw [hy]
    simpa using congrArg (fun L : E →L[𝕜] F => L v)
      (hasFDerivAt_const (𝕜 := 𝕜) (0 : F) y).fderiv
  unfold second
  rw [he.fderiv_eq]
  simp

private theorem second_graph {h : E → F} {x : E} (hh : ContDiffAt 𝕜 2 h x) (v w : E) :
    second (𝕜 := 𝕜) (fun y => (y, h y)) x v w =
      (0, second (𝕜 := 𝕜) h x v w) := by
  have he : (fun y => fderiv 𝕜 (fun y => (y, h y)) y v) =ᶠ[𝓝 x]
      (fun y => (v, fderiv 𝕜 h y v)) := by
    filter_upwards [hh.eventually (by norm_num)] with y hy
    have hp := (hasFDerivAt_id y).prodMk (hy.differentiableAt (by norm_num)).hasFDerivAt
    change HasFDerivAt (fun y : E => (y, h y)) _ y at hp
    rw [hp.fderiv]
    simp
  unfold second
  rw [he.fderiv_eq]
  have hh₂ : DifferentiableAt 𝕜 (fderiv 𝕜 h) x :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hp := (hasFDerivAt_const (𝕜 := 𝕜) v x).prodMk
    (hh₂.clm_apply (differentiableAt_const v)).hasFDerivAt
  rw [hp.fderiv]
  simp

private theorem implicit_first_graph {h : E → F} {F₀ : E × F → G} {x : E}
    (hh : ContDiffAt 𝕜 2 h x) (hF : ContDiffAt 𝕜 2 F₀ (x, h x))
    (he : (fun y => F₀ (y, h y)) =ᶠ[𝓝 x] fun _ => 0) (v : E) :
    fderiv 𝕜 F₀ (x, h x) (v, fderiv 𝕜 h x v) = 0 := by
  have hh₁ := hh.differentiableAt (by norm_num)
  have hF₁ := hF.differentiableAt (by norm_num)
  have hd : fderiv 𝕜 (fun y => F₀ (y, h y)) x = 0 := by
    rw [he.fderiv_eq]
    simp
  have hp := (hasFDerivAt_id x).prodMk hh₁.hasFDerivAt
  change HasFDerivAt (fun y : E => (y, h y)) _ x at hp
  have hc := hF₁.hasFDerivAt.comp x hp
  change HasFDerivAt (fun y : E => F₀ (y, h y)) _ x at hc
  rw [hc.fderiv] at hd
  have hv := congrArg (fun L : E →L[𝕜] G => L v) hd
  simpa using hv

private theorem implicit_second_graph {h : E → F} {F₀ : E × F → G} {x : E}
    (hh : ContDiffAt 𝕜 2 h x) (hF : ContDiffAt 𝕜 2 F₀ (x, h x))
    (he : (fun y => F₀ (y, h y)) =ᶠ[𝓝 x] fun _ => 0) (v w : E) :
    second (𝕜 := 𝕜) F₀ (x, h x) (v, fderiv 𝕜 h x v) (w, fderiv 𝕜 h x w) +
      fderiv 𝕜 F₀ (x, h x) (0, second (𝕜 := 𝕜) h x v w) = 0 := by
  have hh₁ := hh.differentiableAt (by norm_num)
  have hp : ContDiffAt 𝕜 2 (fun y => (y, h y)) x := contDiffAt_id.prodMk hh
  have hs := second_comp (𝕜 := 𝕜) (fun y => (y, h y)) F₀ x v w hp hF
  have hp' := (hasFDerivAt_id x).prodMk hh₁.hasFDerivAt
  change HasFDerivAt (fun y : E => (y, h y)) _ x at hp'
  rw [second_graph hh v w, hp'.fderiv] at hs
  simp only [fderiv_id, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply] at hs
  rw [← hs]
  exact second_eq_zero_of_eventually he v w

theorem implicit_first_scalar {h : E → 𝕜} {F₀ : E × 𝕜 → 𝕜} {x : E}
    (hh : ContDiffAt 𝕜 2 h x) (hF : ContDiffAt 𝕜 2 F₀ (x, h x))
    (he : (fun y => F₀ (y, h y)) =ᶠ[𝓝 x] fun _ => 0)
    (hq : fderiv 𝕜 F₀ (x, h x) (0, 1) ≠ 0) (v : E) :
    fderiv 𝕜 h x v = -fderiv 𝕜 F₀ (x, h x) (v, 0) /
      fderiv 𝕜 F₀ (x, h x) (0, 1) := by
  have H := implicit_first_graph hh hF he v
  have hp : (v, fderiv 𝕜 h x v) =
      (v, (0 : 𝕜)) + (fderiv 𝕜 h x v) • ((0 : E), (1 : 𝕜)) := by simp
  rw [hp, map_add, map_smul, smul_eq_mul] at H
  apply (eq_div_iff hq).mpr
  linear_combination H

theorem implicit_second_scalar {h : E → 𝕜} {F₀ : E × 𝕜 → 𝕜} {x : E}
    (hh : ContDiffAt 𝕜 2 h x) (hF : ContDiffAt 𝕜 2 F₀ (x, h x))
    (he : (fun y => F₀ (y, h y)) =ᶠ[𝓝 x] fun _ => 0)
    (hq : fderiv 𝕜 F₀ (x, h x) (0, 1) ≠ 0) (v w : E) :
    second (𝕜 := 𝕜) h x v w =
      -second (𝕜 := 𝕜) F₀ (x, h x)
        (v, fderiv 𝕜 h x v) (w, fderiv 𝕜 h x w) /
          fderiv 𝕜 F₀ (x, h x) (0, 1) := by
  have H := implicit_second_graph hh hF he v w
  have hp : ((0 : E), second (𝕜 := 𝕜) h x v w) =
      (second (𝕜 := 𝕜) h x v w) • ((0 : E), (1 : 𝕜)) := by simp
  rw [hp, map_smul, smul_eq_mul] at H
  apply (eq_div_iff hq).mpr
  linear_combination H

theorem second_sub_const (f : E → F) (c : F) (x v w : E) :
    second (𝕜 := 𝕜) (fun y => f y - c) x v w = second (𝕜 := 𝕜) f x v w := by
  unfold second
  simp_rw [fderiv_sub_const]

theorem second_comp_clm (L : E →L[𝕜] F) (f : F → G) (x v w : E)
    (hf : ContDiffAt 𝕜 2 f (L x)) :
    second (𝕜 := 𝕜) (f ∘ L) x v w = second (𝕜 := 𝕜) f (L x) (L v) (L w) := by
  have hL : ContDiffAt 𝕜 2 L x := L.contDiff.contDiffAt
  have hs := second_comp (𝕜 := 𝕜) L f x v w hL hf
  have hsecond : second (𝕜 := 𝕜) L x v w = 0 := by
    unfold second
    simp [L.fderiv]
  simpa only [L.fderiv, hsecond, map_zero, add_zero] using hs

section Angular

variable {n : ℕ}

private theorem second_eq_derivative {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hf : ContDiffAt ℂ 2 f x) (v w : Fin n → ℂ) :
    second (𝕜 := ℂ) f x v w = fderiv ℂ (fderiv ℂ f) x w v := by
  have hd : DifferentiableAt ℂ (fderiv ℂ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  unfold second
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem second_sub_sub {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hf : ContDiffAt ℂ 2 f x) (a b c d : Fin n → ℂ) :
    second (𝕜 := ℂ) f x (a - b) (c - d) =
      second (𝕜 := ℂ) f x a c - second (𝕜 := ℂ) f x a d -
        second (𝕜 := ℂ) f x b c + second (𝕜 := ℂ) f x b d := by
  simp only [second_eq_derivative hf, map_sub, _root_.sub_apply]
  abel

private theorem second_complex_to_real {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hf : ContDiffAt ℂ 2 f x) (v w : Fin n → ℂ) :
    second (𝕜 := ℝ) f x v w = second (𝕜 := ℂ) f x v w := by
  have hrestrict := congrArg (fun L => L ![w, v])
    (hf.restrictScalars_iteratedFDeriv (𝕜 := ℝ))
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.restrict_scalars ℝ).fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  rw [second_eq_derivative hf]
  unfold second
  rw [fderiv_clm_apply hd (differentiableAt_const v)]
  simpa only [Function.comp_apply, ContinuousMultilinearMap.coe_restrictScalars,
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, fderiv_const_apply, _root_.zero_apply, map_zero, zero_add] using hrestrict.symm

private noncomputable def angularMap : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    Complex.I • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j))

private theorem second_angular_substitution {f : (Fin n → ℂ) → ℂ}
    (hf : ContDiffAt ℂ 2 f 0) (j k : Fin n) :
    second (𝕜 := ℝ) (fun θ : Fin n → ℝ => f (angularMap θ)) 0
      (Pi.single j 1) (Pi.single k 1) =
      -second (𝕜 := ℂ) f 0 (Pi.single j 1) (Pi.single k 1) := by
  let L : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) := angularMap
  have hL : ContDiffAt ℝ 2 L 0 := L.contDiff.contDiffAt
  have hs := second_comp (𝕜 := ℝ) L f 0 (Pi.single j 1) (Pi.single k 1)
    hL (by simpa using hf.restrict_scalars ℝ)
  have hsecond : second (𝕜 := ℝ) L 0 (Pi.single j 1) (Pi.single k 1) = 0 := by
    unfold second
    simp [L.fderiv]
  rw [hsecond] at hs
  simp only [map_zero, add_zero, L.fderiv] at hs
  change second (𝕜 := ℝ) (f ∘ L) 0 (Pi.single j 1) (Pi.single k 1) = _
  rw [hs, second_complex_to_real hf]
  have hLj : L (Pi.single j 1) = Complex.I • (Pi.single j (1 : ℂ)) := by
    ext i
    by_cases hij : i = j <;> simp [L, angularMap, Pi.single_apply, hij]
  have hLk : L (Pi.single k 1) = Complex.I • (Pi.single k (1 : ℂ)) := by
    ext i
    by_cases hik : i = k <;> simp [L, angularMap, Pi.single_apply, hik]
  rw [hLj, hLk, second_eq_derivative hf, second_eq_derivative hf]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul, smul_eq_mul]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

private noncomputable def logarithmicPhase (a : ℂ) (h : (Fin n → ℂ) → ℂ)
    (u : Fin n → ℂ) : ℂ := Complex.log (h (fun j => a * Complex.exp (u j)))

private theorem logarithmicPhase_smooth {a : ℂ} {h : (Fin n → ℂ) → ℂ}
    (hh : ContDiffAt ℂ 2 h (fun _ => a))
    (ha : h (fun _ => a) ∈ Complex.slitPlane) :
    ContDiffAt ℂ 2 (logarithmicPhase a h) 0 := by
  have he : ContDiff ℂ 2 (fun u : Fin n → ℂ => fun j => a * Complex.exp (u j)) := by
    fun_prop
  have hs : ContDiffAt ℂ 2 (fun u : Fin n → ℂ => h (fun j => a * Complex.exp (u j))) 0 := by
    have hh' : ContDiffAt ℂ 2 h ((fun u : Fin n → ℂ => fun j => a * Complex.exp (u j)) 0) := by simpa using hh
    exact hh'.comp 0 he.contDiffAt
  have hl : ContDiffAt ℂ 2 Complex.log ((fun u : Fin n → ℂ => h (fun j => a * Complex.exp (u j))) 0) := by simpa using Complex.contDiffAt_log (n := 2) ha
  exact hl.comp 0 hs

private noncomputable def exponentialChart (a : ℂ) (u : Fin n → ℂ) : Fin n → ℂ :=
  fun j => a * Complex.exp (u j)

private theorem fderiv_exponentialChart (a : ℂ) (u v : Fin n → ℂ) :
    fderiv ℂ (exponentialChart a) u v = fun j => a * Complex.exp (u j) * v j := by
  have hd : HasFDerivAt (exponentialChart a)
      (ContinuousLinearMap.pi fun j => a • (Complex.exp (u j) • (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ))) u := by
    change HasFDerivAt (fun u : Fin n → ℂ => fun j => a * Complex.exp (u j)) _ u
    apply hasFDerivAt_pi.mpr
    intro j
    exact ((hasFDerivAt_apply (𝕜 := ℂ) j u).cexp).const_mul a
  rw [hd.fderiv]
  ext j
  simp [mul_assoc]

private theorem second_exponentialChart (a : ℂ) (v w : Fin n → ℂ) :
    second (𝕜 := ℂ) (exponentialChart a) 0 v w = fun j => a * v j * w j := by
  unfold second
  simp_rw [fderiv_exponentialChart]
  have hd : HasFDerivAt (fun u : Fin n → ℂ => fun j =>
      a * Complex.exp (u j) * v j)
      (ContinuousLinearMap.pi fun j => (v j) • (a •
        (Complex.exp ((0 : Fin n → ℂ) j) • (ContinuousLinearMap.proj j : (Fin n → ℂ) →L[ℂ] ℂ)))) 0 := by
    apply hasFDerivAt_pi.mpr
    intro j
    exact (((hasFDerivAt_apply (𝕜 := ℂ) j (0 : Fin n → ℂ)).cexp).const_mul a).mul_const (v j)
  rw [hd.fderiv]
  ext j
  simp [mul_assoc, mul_left_comm, mul_comm]

private theorem second_clog {g : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (hg : ContDiffAt ℂ 2 g x) (hslit : g x ∈ Complex.slitPlane)
    (v w : Fin n → ℂ) :
    second (𝕜 := ℂ) (fun y => Complex.log (g y)) x v w =
      -(g x ^ 2)⁻¹ * fderiv ℂ g x w * fderiv ℂ g x v +
      (g x)⁻¹ * second (𝕜 := ℂ) g x v w := by
  have hg₁ := hg.differentiableAt (by norm_num)
  have hg₂ : DifferentiableAt ℂ (fderiv ℂ g) x :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have he : (fun y => fderiv ℂ (fun y => Complex.log (g y)) y v) =ᶠ[𝓝 x]
      (fun y => (g y)⁻¹ * fderiv ℂ g y v) := by
    filter_upwards [hg.eventually (by norm_num),
      hg₁.continuousAt (Complex.isOpen_slitPlane.mem_nhds hslit)] with y hy hys
    have hys' : g y ∈ Complex.slitPlane := hys
    rw [((hy.differentiableAt (by norm_num)).hasFDerivAt.clog hys').fderiv]
    simp
  have hg0 : g x ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hi := (hasDerivAt_inv hg0).comp_hasFDerivAt x hg₁.hasFDerivAt
  have hdv := hg₂.clm_apply (differentiableAt_const (c := v))
  change HasFDerivAt (fun y => (g y)⁻¹) _ x at hi
  have hp := hi.mul hdv.hasFDerivAt
  change HasFDerivAt (fun y => (g y)⁻¹ * fderiv ℂ g y v) _ x at hp
  unfold second
  rw [he.fderiv_eq, hp.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  ring

private theorem logarithmicPhase_second {a : ℂ} {h : (Fin n → ℂ) → ℂ}
    (ha : a ≠ 0) (hh : ContDiffAt ℂ 2 h (fun _ => a))
    (hh0 : h (fun _ => a) = a) (hslit : a ∈ Complex.slitPlane)
    (j k : Fin n) :
    second (𝕜 := ℂ) (logarithmicPhase a h) 0 (Pi.single j 1) (Pi.single k 1) =
      a * second (𝕜 := ℂ) h (fun _ => a) (Pi.single j 1) (Pi.single k 1) +
        (if j = k then fderiv ℂ h (fun _ => a) (Pi.single j 1) else 0) -
          fderiv ℂ h (fun _ => a) (Pi.single j 1) *
            fderiv ℂ h (fun _ => a) (Pi.single k 1) := by
  let e : (Fin n → ℂ) → (Fin n → ℂ) := exponentialChart a
  have he0 : e 0 = (fun _ => a) := by ext i; simp [e, exponentialChart]
  have he : ContDiffAt ℂ 2 e 0 := by
    change ContDiffAt ℂ 2 (fun u : Fin n → ℂ => fun j => a * Complex.exp (u j)) 0
    fun_prop
  have hh' : ContDiffAt ℂ 2 h (e 0) := by simpa [he0] using hh
  have hg : ContDiffAt ℂ 2 (h ∘ e) 0 := hh'.comp 0 he
  have hD1 (v : Fin n → ℂ) : fderiv ℂ (h ∘ e) 0 v =
      a * fderiv ℂ h (fun _ => a) v := by
    rw [fderiv_comp 0 (by simpa [he0] using hh.differentiableAt (by norm_num))
      (he.differentiableAt (by norm_num))]
    simp only [ContinuousLinearMap.comp_apply, he0]
    have heD : fderiv ℂ e 0 v = a • v := by
      ext i
      simp [e, fderiv_exponentialChart]
    rw [heD, map_smul, smul_eq_mul]
  have hD2 := second_comp (𝕜 := ℂ) e h 0 (Pi.single j 1) (Pi.single k 1) he
    (by simpa [he0] using hh)
  rw [he0] at hD2
  have heDj : fderiv ℂ e 0 (Pi.single j 1) = a • (Pi.single j (1 : ℂ)) := by
    ext i
    simp [e, fderiv_exponentialChart]
  have heDk : fderiv ℂ e 0 (Pi.single k 1) = a • (Pi.single k (1 : ℂ)) := by
    ext i
    simp [e, fderiv_exponentialChart]
  rw [heDj, heDk] at hD2
  have hscale : second (𝕜 := ℂ) h (fun _ => a)
      (a • (Pi.single j (1 : ℂ))) (a • (Pi.single k (1 : ℂ))) =
      a * a * second (𝕜 := ℂ) h (fun _ => a) (Pi.single j 1) (Pi.single k 1) := by
    simp only [second_eq_derivative hh, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  rw [hscale] at hD2
  have heD2 : second (𝕜 := ℂ) e 0 (Pi.single j 1) (Pi.single k 1) =
      if j = k then a • (Pi.single j (1 : ℂ)) else 0 := by
    rw [show e = exponentialChart a from rfl, second_exponentialChart]
    split_ifs with hjk
    · subst k; ext i; by_cases hi : i = j <;> simp [hi]
    · ext i; by_cases hi : i = j <;> by_cases hk : i = k <;> simp_all
  rw [heD2] at hD2
  have hlog := second_clog hg (by simp [he0, hh0]; exact hslit)
    (Pi.single j 1) (Pi.single k 1)
  change second (𝕜 := ℂ) (logarithmicPhase a h) 0 (Pi.single j 1) (Pi.single k 1) = _ at hlog
  rw [hlog, hD2, hD1, hD1]
  simp only [Function.comp_apply, he0, hh0]
  split_ifs with hjk
  · simp only [map_smul, smul_eq_mul]
    field_simp
    ring
  · simp only [map_zero, add_zero]
    field_simp
    ring

end Angular

end WormaldAnalytic


namespace WormaldAnalytic

theorem actual_hessian {d : ℕ} {A : Fin d → Fin d → Bool}
    {h : (Fin (d - 1) → ℂ) → ℂ} (hd : 3 ≤ d) (hh : IsLocalSolution A h)
    (j k : Fin (d - 1)) :
    hessian h j k =
      fderiv ℂ h (fun _ => z d) (Pi.single j 1) *
          fderiv ℂ h (fun _ => z d) (Pi.single k 1) -
        z d * second (𝕜 := ℂ) h (fun _ => z d) (Pi.single j 1) (Pi.single k 1) -
          (if j = k then fderiv ℂ h (fun _ => z d) (Pi.single j 1) else 0) := by
  have hz0 : z d ≠ 0 := by
    unfold z
    apply div_ne_zero (by norm_num)
    exact_mod_cast (by omega : d ≠ 0)
  have hzs : z d ∈ Complex.slitPlane := by
    rw [show z d = (((2 : ℝ) / d : ℝ) : ℂ) by simp [z]]
    apply Complex.ofReal_mem_slitPlane.mpr
    exact div_pos (by norm_num) (by exact_mod_cast (by omega : 0 < d))
  have hsm := logarithmicPhase_smooth hh.2.1 (by rw [hh.1]; exact hzs)
  have hang := second_angular_substitution hsm j k
  change hessian h j k =
    -second (𝕜 := ℂ) (logarithmicPhase (z d) h) 0 (Pi.single j 1) (Pi.single k 1) at hang
  rw [hang, logarithmicPhase_second hz0 hh.2.1 hh.1 hzs]
  ring

end WormaldAnalytic

end D5.S3.Combinatorics.WormaldTournamentHessian.Defs
