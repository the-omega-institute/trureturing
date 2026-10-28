import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.EulerLayerInventoryGrowth
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth

open _root_.D5.S3.Arith.Robin.EulerLayerInventoryGrowth
open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Chebyshev

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ U => Real.log U) (fun e => nomatch e)

def finiteRejected : Realization signature :=
  realize signature (fun _ _ _ => -(|θ 2 - Real.log 2| + 1)) (fun e => nomatch e)

def growthRejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev finiteArena : Arena where
  signature := signature
  Law R := ∀ {t : ℝ}, 2 ≤ t → ∀ {U : ℕ}, 0 < U →
    (∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
    θ t - Real.log t ≤ R.readout () () U ∧
      Real.log U ≤ θ t + ψ (t * Real.log t / Real.log 2) -
        θ (t * Real.log t / Real.log 2)

private theorem finite_rejected : ¬ finiteArena.Law finiteRejected := by
  intro h
  have hp : 0 < 1 / ((2 : ℝ) * Real.log 2) :=
    one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  obtain ⟨U, hU, hstrict, _⟩ := optimal_layer_count_spec hp
  have hh := (h (t := 2) (by norm_num) (U := U) (by omega)
    (fun q _ => hstrict q)).1
  change θ 2 - Real.log 2 ≤ -(|θ 2 - Real.log 2| + 1) at hh
  linarith [neg_abs_le (θ 2 - Real.log 2)]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change Real.log (1 : ℕ) ≠ Real.log (2 : ℕ)
  norm_cast
  simp only [Real.log_one, ne_eq]
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

def finiteFamily : Registration finiteArena (type_of% @strict_inventory_chebyshev_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strict_inventory_chebyshev_bounds, finiteRejected, finite_rejected⟩
  sensitivity := ⟨fun i => ⟨finiteRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, finite_rejected⟩,
    fun i => nomatch i⟩
  dependence := dependence

abbrev growthArena : Arena where
  signature := signature
  Law R := ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t → ∀ U : ℕ, 0 < U →
    (∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
    |R.readout () () U / t - 1| < ε

private theorem growth_rejected : ¬ growthArena.Law growthRejected := by
  intro h
  obtain ⟨T, _, hT⟩ := h 1 (by norm_num)
  let t := max T 2
  have ht : 1 < t := lt_of_lt_of_le (by norm_num) (le_max_right T 2)
  have hp : 0 < 1 / (t * Real.log t) :=
    one_div_pos.mpr (mul_pos (by linarith) (Real.log_pos ht))
  obtain ⟨U, hU, hstrict, _⟩ := optimal_layer_count_spec hp
  have hh := hT t (le_max_left T 2) U (by omega) (fun q _ => hstrict q)
  change |(0 : ℝ) / t - 1| < 1 at hh
  norm_num at hh

def growthFamily : Registration growthArena (type_of% strict_inventory_uniform_growth) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strict_inventory_uniform_growth, growthRejected, growth_rejected⟩
  sensitivity := ⟨fun i => ⟨growthRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, growth_rejected⟩,
    fun i => nomatch i⟩
  dependence := dependence

def finiteAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_inventory_chebyshev_bounds) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth.strict_inventory_chebyshev_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth.finiteFamily
  realizationSource := none
  generated := false
  arena := .source ⟨finiteArena⟩
  objectArena := .source ⟨finiteArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteArena ⟨finiteFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def growthAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_inventory_uniform_growth) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth.strict_inventory_uniform_growth.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth.growthFamily
  realizationSource := none
  generated := false
  arena := .source ⟨growthArena⟩
  objectArena := .source ⟨growthArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source growthArena ⟨growthFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms finiteFamily
#print axioms growthFamily

def higherActual : Realization signature :=
  realize signature (fun _ _ U =>
    ∑ q ∈ U.primeFactors, ((U.factorization q - 1 : ℕ) : ℝ) * Real.log q)
    (fun e => nomatch e)

def higherRejected : Realization signature :=
  realize signature (fun _ _ _ =>
    2 * θ (Real.sqrt (2 * 2)) + 2 * (ψ 2 - θ 2) + 1)
    (fun e => nomatch e)

abbrev higherArena : Arena where
  signature := signature
  Law R := ∀ {t : ℝ}, 2 ≤ t → ∀ {U : ℕ}, 0 < U →
    (∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
    R.readout () () U ≤ 2 * θ (Real.sqrt (2 * t)) + 2 * (ψ t - θ t)

private theorem higher_rejected : ¬ higherArena.Law higherRejected := by
  intro h
  have hp : 0 < 1 / ((2 : ℝ) * Real.log 2) :=
    one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos (by norm_num)))
  obtain ⟨U, hU, hstrict, _⟩ := optimal_layer_count_spec hp
  have hh := h (t := 2) (by norm_num) (U := U) (by omega) (fun q _ => hstrict q)
  change 2 * θ (Real.sqrt (2 * 2)) + 2 * (ψ 2 - θ 2) + 1 ≤
    2 * θ (Real.sqrt (2 * 2)) + 2 * (ψ 2 - θ 2) at hh
  linarith

private theorem higher_dependence : ObservationalDependence signature higherActual := by
  intro i
  refine ⟨(), 1, 4, ?_⟩
  change (∑ q ∈ (1 : ℕ).primeFactors,
      (((1 : ℕ).factorization q - 1 : ℕ) : ℝ) * Real.log q) ≠
    ∑ q ∈ (4 : ℕ).primeFactors,
      (((4 : ℕ).factorization q - 1 : ℕ) : ℝ) * Real.log q
  have hone : (1 : ℕ).primeFactors = ∅ := by simp
  have hfour : (4 : ℕ).primeFactors = {2} := by
    change ((2 : ℕ) ^ 2).primeFactors = {2}
    exact Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two
  have hval : (4 : ℕ).factorization 2 = 2 := by
    change ((2 : ℕ) ^ 2).factorization 2 = 2
    exact Nat.factorization_pow_self Nat.prime_two
  simp only [hone, Finset.sum_empty, hfour, Finset.sum_singleton, hval]
  norm_num
  exact (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne

def higherFamily : Registration higherArena (type_of% @strict_inventory_higher_layer_bound) where
  actual := higherActual
  bridge := Iff.rfl
  variation := ⟨strict_inventory_higher_layer_bound, higherRejected, higher_rejected⟩
  sensitivity := ⟨fun i => ⟨higherRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, higher_rejected⟩,
    fun i => nomatch i⟩
  dependence := higher_dependence

abbrev sqrtArena : Arena where
  signature := signature
  Law R := ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 2 ≤ t → ∀ U : ℕ, 0 < U →
    (∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q) →
    |R.readout () () U - ψ t| ≤ C * Real.sqrt t

private theorem sqrt_rejected : ¬ sqrtArena.Law growthRejected := by
  intro h
  obtain ⟨C, hC, hbad⟩ := h
  obtain ⟨c, hc, hactual⟩ := strict_inventory_sqrt_discrepancy
  obtain ⟨T, _, hgrowth⟩ := strict_inventory_uniform_growth (1 / 2) (by norm_num)
  let s : ℝ := |T| + 2 * C + 2 * c + 4
  have hs : 4 < s := by dsimp [s]; linarith [abs_nonneg T]
  have hTs : T ≤ s := by dsimp [s]; linarith [le_abs_self T]
  have hss : s ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 1)]
  let t : ℝ := s ^ 2
  have ht2 : 2 ≤ t := by dsimp [t]; linarith
  have htT : T ≤ t := hTs.trans hss
  have ht0 : 0 < t := by linarith
  have hp : 0 < 1 / (t * Real.log t) :=
    one_div_pos.mpr (mul_pos ht0 (Real.log_pos (by linarith)))
  obtain ⟨U, hU, hstrict, _⟩ := optimal_layer_count_spec hp
  have hU0 : 0 < U := by omega
  have hUstrict : ∀ q : ℕ, q.Prime →
      U.factorization q = optimalLayerCount (1 / (t * Real.log t)) q :=
    fun q _ => hstrict q
  have hb := hbad t ht2 U hU0 hUstrict
  change |0 - ψ t| ≤ C * Real.sqrt t at hb
  have hpsi : ψ t ≤ C * Real.sqrt t := by
    have hh := (abs_le.mp hb).1
    linarith
  have ha := (abs_le.mp (hactual t ht2 U hU0 hUstrict)).2
  have hg := (abs_lt.mp (hgrowth t htT U hU0 hUstrict)).1
  have hratio : (1 / 2 : ℝ) < Real.log U / t := by linarith
  have hlog : t / 2 < Real.log U := by
    have hh := (lt_div_iff₀ ht0).mp hratio
    linarith
  have hroot : Real.sqrt t = s := by
    dsimp [t]
    exact Real.sqrt_sq (by linarith)
  rw [hroot] at hpsi ha
  have hsc : 2 * (C + c) < s := by dsimp [s]; linarith [abs_nonneg T]
  dsimp [t] at hlog
  nlinarith

def sqrtFamily : Registration sqrtArena (type_of% strict_inventory_sqrt_discrepancy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨strict_inventory_sqrt_discrepancy, growthRejected, sqrt_rejected⟩
  sensitivity := ⟨fun i => ⟨growthRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, sqrt_rejected⟩,
    fun i => nomatch i⟩
  dependence := dependence

def higherAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_inventory_higher_layer_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth.strict_inventory_higher_layer_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth.higherFamily
  realizationSource := none
  generated := false
  arena := .source ⟨higherArena⟩
  objectArena := .source ⟨higherArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source higherArena ⟨higherFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature higherActual.readout higherActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def sqrtAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@strict_inventory_sqrt_discrepancy) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth.strict_inventory_sqrt_discrepancy.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth.sqrtFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sqrtArena⟩
  objectArena := .source ⟨sqrtArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sqrtArena ⟨sqrtFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms higherFamily
#print axioms sqrtFamily

end

noncomputable section

abbrev logSplitArena : Arena where
  signature := signature
  Law R := ∀ {U : ℕ}, 0 < U →
    R.readout () () U = (∑ p ∈ U.primeFactors, Real.log p) +
      ∑ p ∈ U.primeFactors, ((U.factorization p - 1 : ℕ) : ℝ) * Real.log p

private theorem log_split_rejected : ¬ logSplitArena.Law growthRejected := by
  intro h
  have hh := h (U := 2) (by norm_num)
  have ha := log_factorization_split (U := 2) (by norm_num)
  change 0 = _ at hh
  have hlog := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  norm_num only [Nat.cast_ofNat] at ha
  linarith only [ha, hh, hlog]

def logSplitFamily : Registration logSplitArena (type_of% @log_factorization_split) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨log_factorization_split, growthRejected, log_split_rejected⟩
  sensitivity := ⟨fun i => ⟨growthRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, log_split_rejected⟩,
    fun i => nomatch i⟩
  dependence := dependence

abbrev massMonoArena : Arena where
  signature := signature
  Law R := ∀ {A B : ℕ}, 0 < A → 0 < B → A ∣ B →
    R.readout () () A ≤ R.readout () () B

def massMonoRejected : Realization signature :=
  realize signature (fun _ _ U => -(U : ℝ)) (fun e => nomatch e)

private theorem mass_mono_rejected : ¬ massMonoArena.Law massMonoRejected := by
  intro h
  have hh := h (A := 1) (B := 2) (by norm_num) (by norm_num) (by norm_num)
  norm_num [massMonoRejected, realize] at hh

def massMonoFamily : Registration massMonoArena (type_of% @higher_layer_mass_mono) where
  actual := higherActual
  bridge := Iff.rfl
  variation := ⟨higher_layer_mass_mono, massMonoRejected, mass_mono_rejected⟩
  sensitivity := ⟨fun i => ⟨massMonoRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, mass_mono_rejected⟩,
    fun i => nomatch i⟩
  dependence := higher_dependence

def logSplitAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_factorization_split) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth.log_factorization_split.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth.logSplitFamily
  realizationSource := none
  generated := false
  arena := .source ⟨logSplitArena⟩
  objectArena := .source ⟨logSplitArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logSplitArena ⟨logSplitFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def massMonoAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@higher_layer_mass_mono) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth.higher_layer_mass_mono.audit
  realizationName := `Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth.massMonoFamily
  realizationSource := none
  generated := false
  arena := .source ⟨massMonoArena⟩
  objectArena := .source ⟨massMonoArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source massMonoArena ⟨massMonoFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature higherActual.readout higherActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.EulerLayerInventoryGrowth
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Arith.Robin.EulerLayerInventoryGrowth
