import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.MixedTripleExclusion
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped Matrix Classical
namespace Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion
open _root_.D5.S3.Observer.CubicGain.MixedTripleExclusion
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (List Bool)
    (fun _ => Finset World3) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ v T => decide (Losing 5 T v)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a₀ j m b : ℝ) (_hℓ : m-j ≠ 0)
    (v : List Bool) (_hv : v = [true,false] ∨ v = [false,true])
    (T : Finset World3) (_hT : T.card = 3)
    (_hP : ∀ W ∈ T, ∀ Z ∈ T, W ≠ Z → W.source ≠ Z.source)
    (_hreads : ∀ W ∈ T, readAt W [] 0 = a₀ ∧ readAt W [true] 1 = j ∧
      readAt W [false] 1 = m ∧ readAt W v 2 = b), ¬ R.readout () v T = true

private def legalWorld (x r : ℝ) (hx : 0 < x) (hr : 0 < r)
    (c : Coeff 3) (hc : c ≠ 0) (d : ℝ) : World3 :=
  ⟨sourceChart x r, source_chart_legal x r hx hr, c, hc, d⟩

private def goodA : World3 := legalWorld 1 (1/3) (by norm_num) (by norm_num)
  ![4,6/7,-6/7,0] (by intro h; have := congrFun h 0; norm_num at this) (-4)
private def goodB : World3 := legalWorld (1/2) (1/2) (by norm_num) (by norm_num)
  ![4,18/7,-11/7,0] (by intro h; have := congrFun h 0; norm_num at this) (-4)
private def goodC : World3 := legalWorld (1/3) 1 (by norm_num) (by norm_num)
  ![4,2/5,-2/5,0] (by intro h; have := congrFun h 0; norm_num at this) (-4)
private def goodSupport : Finset World3 := {goodA,goodB,goodC}

private theorem good_distinct : goodA ≠ goodB ∧ goodA ≠ goodC ∧ goodB ≠ goodC := by
  constructor
  · intro h
    have := congrArg (fun W : World3 => W.source 0 1) h
    norm_num [goodA,goodB,legalWorld,sourceChart] at this
  constructor
  · intro h
    have := congrArg (fun W : World3 => W.source 0 1) h
    norm_num [goodA,goodC,legalWorld,sourceChart] at this
  · intro h
    have := congrArg (fun W : World3 => W.source 0 1) h
    norm_num [goodB,goodC,legalWorld,sourceChart] at this

private theorem good_card : goodSupport.card = 3 := by
  simp [goodSupport,good_distinct.1,good_distinct.2.1,good_distinct.2.2]

private theorem good_sources : ∀ W ∈ goodSupport, ∀ Z ∈ goodSupport,
    W ≠ Z → W.source ≠ Z.source := by
  intro W hW Z hZ hne
  simp only [goodSupport,Finset.mem_insert,Finset.mem_singleton] at hW hZ
  rcases hW with rfl | rfl | rfl <;> rcases hZ with rfl | rfl | rfl
  all_goals try exact (hne rfl).elim
  all_goals
    intro h
    have := congrArg (fun P : Mat => P 0 1) h
    norm_num [goodA,goodB,goodC,legalWorld,sourceChart] at this

private theorem good_reads : ∀ W ∈ goodSupport,
    readAt W [] 0 = 0 ∧ readAt W [true] 1 = 0 ∧
      readAt W [false] 1 = 1 ∧ readAt W [false,true] 2 = 0 := by
  intro W hW
  simp only [goodSupport,Finset.mem_insert,Finset.mem_singleton] at hW
  rcases hW with rfl | rfl | rfl
  all_goals
    norm_num [goodA,goodB,goodC,legalWorld,readAt,gain,
      Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four,acquisition,Raw,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      sourceChart,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 1 0 (by norm_num) [false,true] (Or.inr rfl)
    goodSupport good_card good_sources good_reads rfl

/-- Legal sources with a common cubic shape; their parent readings are not the
four common readings in the exclusion law. -/
private def testA : World3 := legalWorld 1 (1/4) (by norm_num) (by norm_num)
  ![-840,470,-85,5] (by intro h; have := congrFun h 0; norm_num at this) 0
private def testB : World3 := legalWorld (1/3) (1/2) (by norm_num) (by norm_num)
  ![-1176,658,-119,7] (by intro h; have := congrFun h 0; norm_num at this) 0
private def testC : World3 := legalWorld (1/2) (1/3) (by norm_num) (by norm_num)
  ![-1176,658,-119,7] (by intro h; have := congrFun h 0; norm_num at this) 0
private def testSupport : Finset World3 := {testA,testB,testC}

private theorem test_distinct : testA ≠ testB ∧ testA ≠ testC ∧ testB ≠ testC := by
  constructor
  · intro h
    have := congrArg (fun W : World3 => W.source 0 1) h
    norm_num [testA,testB,legalWorld,sourceChart] at this
  constructor
  · intro h
    have := congrArg (fun W : World3 => W.source 0 1) h
    norm_num [testA,testC,legalWorld,sourceChart] at this
  · intro h
    have := congrArg (fun W : World3 => W.source 0 1) h
    norm_num [testB,testC,legalWorld,sourceChart] at this

private theorem test_card : testSupport.card = 3 := by
  simp [testSupport,test_distinct.1,test_distinct.2.1,test_distinct.2.2]

private theorem test_root_read (W : World3) (hW : W ∈ testSupport)
    (v : List Bool) (k : ℕ) (hk : k = 4 ∨ k = 6 ∨ k = 7) : readAt W v k = 0 := by
  simp only [testSupport,Finset.mem_insert,Finset.mem_singleton] at hW
  rcases hW with rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl
  all_goals
    norm_num [testA,testB,testC,legalWorld,readAt,gain,
      Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four]

private theorem test_third_read (E : Bool) (W : World3) (hW : W ∈ testSupport) :
    readAt W ([false,true] ++ [E]) 3 = if E then -72 else -84 := by
  simp only [testSupport,Finset.mem_insert,Finset.mem_singleton] at hW
  rcases hW with rfl | rfl | rfl <;> cases E
  all_goals
    norm_num [testA,testB,testC,legalWorld,readAt,gain,
      Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four,acquisition,Raw,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      sourceChart,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two]

private theorem test_two (S : Finset World3) (hS : S ⊆ testSupport)
    (hcard : 2 ≤ S.card) (v : List Bool) (hv : v.length = 5) : Losing 2 S v := by
  refine ⟨hcard, ?_⟩
  intro E
  refine ⟨0, ?_⟩
  have hsix : responseSlice S v E 0 = S := by
    apply Finset.filter_eq_self.mpr
    intro W hW
    change readAt W (v ++ [E]) (v.length+1) = 0
    rw [hv]
    exact test_root_read W (hS hW) _ 6 (Or.inr (Or.inl rfl))
  rw [hsix]
  refine ⟨hcard, ?_⟩
  intro F
  refine ⟨0, ?_⟩
  have hseven : responseSlice S (v ++ [E]) F 0 = S := by
    apply Finset.filter_eq_self.mpr
    intro W hW
    change readAt W ((v ++ [E]) ++ [F]) ((v ++ [E]).length+1) = 0
    simp only [List.length_append,List.length_singleton,hv]
    exact test_root_read W (hS hW) _ 7 (Or.inr (Or.inr rfl))
  rw [hseven]
  exact hcard

private theorem fifth_child (E F G : Bool) (z : ℝ)
    (W Z : World3) (hW : W ∈ testSupport) (hZ : Z ∈ testSupport) (hne : W ≠ Z)
    (hrW : readAt W ([false,true] ++ [E] ++ [F] ++ [G]) 5 = z)
    (hrZ : readAt Z ([false,true] ++ [E] ++ [F] ++ [G]) 5 = z) :
    Losing 2 (responseSlice testSupport ([false,true] ++ [E] ++ [F]) G z)
      ([false,true] ++ [E] ++ [F] ++ [G]) := by
  apply test_two _ (Finset.filter_subset _ _) _ _ (by simp)
  have hW' : W ∈ responseSlice testSupport ([false,true] ++ [E] ++ [F]) G z := by
    exact Finset.mem_filter.mpr ⟨hW,by simpa using hrW⟩
  have hZ' : Z ∈ responseSlice testSupport ([false,true] ++ [E] ++ [F]) G z := by
    exact Finset.mem_filter.mpr ⟨hZ,by simpa using hrZ⟩
  exact Finset.one_lt_card.mpr ⟨W,hW',Z,hZ',hne⟩

private theorem test_fifth (E F G : Bool) : ∃ z : ℝ,
    Losing 2 (responseSlice testSupport ([false,true] ++ [E] ++ [F]) G z)
      ([false,true] ++ [E] ++ [F] ++ [G]) := by
  have ha : testA ∈ testSupport := by simp [testSupport]
  have hb : testB ∈ testSupport := by simp [testSupport]
  have hc : testC ∈ testSupport := by simp [testSupport]
  cases E <;> cases F <;> cases G
  · refine ⟨46,fifth_child false false false 46 testA testB ha hb test_distinct.1 ?_ ?_⟩
  · refine ⟨38,fifth_child false false true 38 testA testC ha hc test_distinct.2.1 ?_ ?_⟩
  · refine ⟨16,fifth_child false true false 16 testA testB ha hb test_distinct.1 ?_ ?_⟩
  · refine ⟨14,fifth_child false true true 14 testA testB ha hb test_distinct.1 ?_ ?_⟩
  · refine ⟨38,fifth_child true false false 38 testB testC hb hc test_distinct.2.2 ?_ ?_⟩
  · refine ⟨28,fifth_child true false true 28 testA testB ha hb test_distinct.1 ?_ ?_⟩
  · refine ⟨14,fifth_child true true false 14 testA testB ha hb test_distinct.1 ?_ ?_⟩
  · refine ⟨12,fifth_child true true true 12 testA testB ha hb test_distinct.1 ?_ ?_⟩
  all_goals
    norm_num [testA,testB,testC,legalWorld,readAt,gain,
      Polynomial.ofFn_eq_sum_monomial,Fin.sum_univ_four,acquisition,Raw,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      sourceChart,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_two]

private theorem test_losing : Losing 5 testSupport [false,true] := by
  have hcard : 2 ≤ testSupport.card := by rw [test_card]; norm_num
  refine ⟨hcard, ?_⟩
  intro E
  refine ⟨if E then -72 else -84, ?_⟩
  have hthird : responseSlice testSupport [false,true] E (if E then -72 else -84) = testSupport := by
    apply Finset.filter_eq_self.mpr
    intro W hW
    exact test_third_read E W hW
  rw [hthird]
  refine ⟨hcard, ?_⟩
  intro F
  refine ⟨0, ?_⟩
  have hfourth : responseSlice testSupport ([false,true] ++ [E]) F 0 = testSupport := by
    apply Finset.filter_eq_self.mpr
    intro W hW
    exact test_root_read W hW _ 4 (Or.inl rfl)
  rw [hfourth]
  exact ⟨hcard, fun G => test_fifth E F G⟩

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨[false,true],testSupport,∅,?_⟩
  have he : ¬ Losing 5 (∅ : Finset World3) [false,true] := by
    intro h
    have hg := h.1
    norm_num at hg
  simp [actual,realize,test_losing,he]

private theorem actual_positive : arena.Law actual := by
  intro a₀ j m b hℓ v hv T hT hP hreads hL
  exact mixed_prefix_three_world_exclusion a₀ j m b hℓ v hv T hT hP hreads
    (of_decide_eq_true hL)

private theorem bridge : (type_of% @mixed_prefix_three_world_exclusion) ↔ arena.Law actual := by
  simp only [arena,actual,realize,decide_eq_true_eq]

def source_registration : Registration arena (type_of% @mixed_prefix_three_world_exclusion) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_positive,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@mixed_prefix_three_world_exclusion) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.MixedTripleExclusion.mixed_prefix_three_world_exclusion.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ v T => decide (Losing 5 T v)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.MixedTripleExclusion
    definition := none
    coordinates := #[5]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
#check @mixed_prefix_three_world_exclusion
end Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion
