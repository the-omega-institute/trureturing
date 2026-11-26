import GRH.Lib.Weil.Construction.Projections
-- Adapted from grh-lean (compact edition) for the trureturing module layout.

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Schrödinger model at split places embedded in the vacuum model: Heisenberg action, inner
products. -/

noncomputable section

namespace Space

open NumberField MeasureTheory stdLattice Finset Complex AddChar Matrix IsSchwartzBruhat
variable {E} [Field E] [CMType E] [WeilData E] {n} [Fintype n] {s}
  {S : Set (FinPlace E)} (hS : S.IsConjDisjoint) (V : Space E n s) {Ψ Ψ' : (n → _) → ℂ}
attribute [-simp] map_add
/-- The linear map sending finitely supported c on finite adelic vectors to ∑ c(y) ϱ(αy₊) P^S on
𝒮(V), y₊ the part above S ∪ S̄, P^S = `Space.projOn` S. -/
def heisenbergComb S := Finsupp.lift _ ℂ _ fun y ↦
  V.ϱ (finVec (idem S.conjClosure • y)) ∘L V.projOn S

/-- The linear map Ψ ↦ Ψ⊗ from functions on finite adelic vectors to operators on 𝒮(V):
`Space.heisenbergComb` of chosen coefficients c, with `schrodingerComb` c = Ψ when such exist. -/
def name S := V.heisenbergComb S ∘ₗ (exists_generalized_inverse (schrodingerComb S)).choose

attribute [local simp] finHeisOp idem_apply mem_integralBox idem_mul_self localInner Set.indicator
  Finsupp.sum smul_smul idem_mul_mem_Ô heisenbergComb schrodingerAct_schrodingerAct mem_stdLattice
  star_idem integral_finsetSum integrable_finsetSum mul_sum sum_mul finVec.eq_1

/-- For v in the Fock space and f in 𝒮(V), v⊗(Ψ⊗f) = Ψ⊗(v⊗f): the operators `Space.integrated` v
and `Space.name` S Ψ commute. -/
lemma integrated_name v f : V.integrated v (V.name S Ψ f) =
  V.name S Ψ (V.integrated v f) := by simp [name, rho_integrated]

lemma name_projOn f : V.name S Ψ (V.projOn S f) = V.name S Ψ f := by simp [name, ← projOn_union]

lemma smul_name (c : ℂ) f : c • V.name S Ψ f = V.name S (c • Ψ) f := by simp

/-- If T is a set of finite places disjoint from S ∪ S̄, the projection P^T fixes Ψ⊗vac, for
every function Ψ named at the places of S. -/
lemma projOn_name_vacElem {T} (hT : Disjoint S.conjClosure T) : V.projOn T (V.name S Ψ V.vacElem) =
  V.name S Ψ V.vacElem := by simp (disch := simp; grind [star_star]) [name]

lemma localInner_boxIndicator_mulVec (g : GL n _) : localInner S (boxIndicator n S)
  (boxIndicator n S <| g.1 *ᵥ ·) = (‖glMultiplier (cutGL (idem_mul_self S) g)‖ ^ 2 :)⁻¹ := by
  erw [← latticeMeasure_inter_eq_glMultiplier, ← integral_indicator_one
    (isOpen_stdLattice.preimage_of_continuous.inter isOpen_stdLattice).measurableSet,
    ← integral_complex_ofReal, localInner, ← integral_indicator isOpen_integralBox.measurableSet]
  simp [mem_Ô, cutGL, ↓idem_mul_mem_Ô, apply_ite, ite_apply]; grind

/-- Fourier transform of a translated box: over x integral off S, the integral of 1(x+m)
χ(z*(x+m)_S) c 1(z), with 1 the indicator of integrality on S, is c if z is integral on S ∪
S̄ and 0 otherwise. -/
lemma fourier_boxIndicator {F : _ → ℂ} m z c (h : ∀ x,
  boxIndicator n S (x + m) * psi₀ E (star z ⬝ᵥ idem S • (x + m)) * c * boxIndicator n S z =
  F x) : ∫ x in integralBox n Sᶜ, F x ∂latticeMeasure E n = boxIndicator n S.conjClosure z * c := by
  have := integral_psi₀_stdLattice (star (idem S) • z)
  rw [← setIntegral_add_mem (m := idem S • -m), ← funext h] <;> simp_all [↓integral_mul_const,
    ← integralBox_compl_inter (S := S), ← setIntegral_indicator isOpen_integralBox.measurableSet]
  grind

include hS
attribute [local simp ←] heisRep_right_rho add_assoc map_neg_eq_inv map_add_eq_mul inv_eq_conj

lemma dataInner_heisenbergComb c c' f f' :
  V.dataInner (V.heisenbergComb S c f) (V.heisenbergComb S c' f') = localInner S
  (schrodingerComb S c) (schrodingerComb S c') * V.dataInner (V.projOn S f) (V.projOn S f') := by
  simp [mul_mul_mul_comm,
    (integrableOn (continuous_conj.comp' (locally_constant S).continuous)).const_mul]
  congr! 2 with z - y
  obtain ⟨z, rfl⟩ := add_left_surjective y z
  rw [← dataInner_rho _ (finVec (idem S.conjClosure • -y)), fourier_boxIndicator y z
    (schrodingerAct S (-y) (schrodingerAct S (y + z) (boxIndicator n S)) 0)]
  by_cases hy : z ∈ integralBox n S.conjClosure
  nth_rw 4 [← V.finHeisOp_projOn hy]; have :=
    congrFun (schrodingerAct_boxIndicator hS hy) 0; simp_all; grind
  have := V.projOn_finHeisOp (S.union_self ▸ V.projOn_union f').symm (idem S.conjClosure • z)
  any_goals simp_all [dataInner_projOn, schrodingerAct, integralBox, -mem_stdLattice, apply_ite]
  grind [add_mem_cancel_left]

lemma name_schrodingerComb c f : V.name S (schrodingerComb S c) f = V.heisenbergComb S c f :=
  sub_eq_zero.1 (V.eq_zero_of_dataInner_self
  (by grind [name, dataInner_heisenbergComb, LinearMap.comp_apply]))

@[local simp] lemma name_schrodingerAct_boxIndicator y f :
  V.name S (schrodingerAct S y (boxIndicator n S)) f = V.ϱ (finVec (idem S.conjClosure • y))
  (V.projOn S f) := by simpa using V.name_schrodingerComb hS (.single y 1) f

/-- For a set S of finite places disjoint from its conjugate, the indicator of the vectors
integral at all places of S names the operator P^S = `Space.projOn` S. -/
lemma name_boxIndicator : V.name S (boxIndicator n S) = V.projOn S := by
  simpa [schrodingerAct] using funext (V.name_schrodingerAct_boxIndicator hS 0)

variable [IsSchwartzBruhat S Ψ]

/-- For S disjoint from its conjugate and Ψ Schwartz–Bruhat above S, ϱ(αy₊)(Ψ ⊗ f) = Ψ′ ⊗ f,
where y₊ is the part of y above S ∪ S̄ and Ψ′ = `schrodingerAct` S y Ψ. -/
lemma ϱ_name y f : V.ϱ (finVec (idem S.conjClosure • y)) (V.name S Ψ f) =
  V.name S (schrodingerAct S y Ψ) f := by cases exists_schrodingerComb_eq hS ‹_›; aesop

/-- For S disjoint from its conjugate and Ψ, Ψ′ Schwartz–Bruhat above S, ⟨Ψ ⊗ f, Ψ′ ⊗ f′⟩ equals the
inner product of Ψ and Ψ′ above S times ⟨P^S f, P^S f′⟩. -/
lemma dataInner_name [IsSchwartzBruhat S Ψ'] f f' : V.dataInner (V.name S Ψ f) (V.name S Ψ' f') =
  localInner S Ψ Ψ' * V.dataInner (V.projOn S f) (V.projOn S f') := by grind [name_schrodingerComb,
  dataInner_heisenbergComb, → exists_schrodingerComb_eq, LinearMap.mem_range]

attribute [irreducible] name
