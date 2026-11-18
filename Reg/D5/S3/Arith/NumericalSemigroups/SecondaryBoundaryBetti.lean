import D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti

open _root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti


private theorem pure_eval (d : Generators) (i : Fin 4) (k : ℕ) :
    eval d (_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure i k) = k * d i := by classical simp [eval,_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure]

/-- Exact finite-coordinate interpretation of the source's generated semigroup. -/
theorem source_semigroup (d : Generators) (n : ℕ) :
    n ∈ semigroup d ↔ ∃ z : Factorization, eval d z = n := by
  classical
  constructor
  · intro hn
    induction hn using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨i,rfl⟩ := hx
      exact ⟨_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure i 1, by simp [pure_eval]⟩
    | zero => exact ⟨0,by simp [eval]⟩
    | add x y _ _ hx hy =>
      obtain ⟨z,rfl⟩ := hx
      obtain ⟨w,rfl⟩ := hy
      exact ⟨z+w,by simp [eval,add_mul,Finset.sum_add_distrib]⟩
  · rintro ⟨z,rfl⟩
    apply AddSubmonoid.sum_mem
    intro i _
    simpa [nsmul_eq_mul] using (semigroup d).nsmul_mem
      (AddSubmonoid.subset_closure (Set.mem_range_self i)) (z i)

/-- The indexed exclusion is exactly the source's exclusion of the other generators. -/
theorem source_excluded_generator (d : Generators) (i : Fin 4) (n : ℕ) :
    n ∈ AddSubmonoid.closure (d '' {j : Fin 4 | j ≠ i}) ↔
      ∃ z : Factorization, z i = 0 ∧ eval d z = n := by
  classical
  constructor
  · intro hn
    induction hn using AddSubmonoid.closure_induction with
    | mem x hx =>
      obtain ⟨j,hji,rfl⟩ := hx
      exact ⟨_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure j 1, by simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,Ne.symm hji], by simp [pure_eval]⟩
    | zero => exact ⟨0,rfl,by simp [eval]⟩
    | add x y _ _ hx hy =>
      obtain ⟨z,hzi,rfl⟩ := hx
      obtain ⟨w,hwi,rfl⟩ := hy
      exact ⟨z+w,by simp [hzi,hwi],by simp [eval,add_mul,Finset.sum_add_distrib]⟩
  · rintro ⟨z,hzi,rfl⟩
    apply AddSubmonoid.sum_mem
    intro j _
    by_cases hji : j = i
    · subst j; simp [hzi]
    · simpa [nsmul_eq_mul] using (AddSubmonoid.closure (d '' {j : Fin 4 | j ≠ i})).nsmul_mem
        (AddSubmonoid.subset_closure ⟨j,hji,rfl⟩) (z j)

/-- The nested gcd used by the binding is the gcd of the source generator set. -/
theorem source_set_gcd (d : Generators) :
    Nat.setGcd (Set.range d) = Nat.gcd (Nat.gcd (d 0) (d 1)) (Nat.gcd (d 2) (d 3)) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd <;> apply Nat.dvd_gcd <;>
      exact Nat.setGcd_dvd_of_mem (Set.mem_range_self _)
  · apply Nat.dvd_setGcd_iff.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_left _ _)
    · exact dvd_trans (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _)
    · exact dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _)

/-- Cofiniteness follows for exactly the unbounded source domain. -/
theorem source_cofinite (d : Generators) (hd : IsNumericalGeneratingTuple d) :
    (↑(semigroup d) : Set ℕ).compl.Finite := by
  obtain ⟨N,hN⟩ := Nat.exists_mem_closure_of_ge (Set.range d)
  apply (Set.finite_Iio N).subset
  intro n hn
  change n < N
  by_contra h
  exact hn (hN n (by omega) (by rw [source_set_gcd, hd.2.1]; exact one_dvd _))

/-- Minimal indexed generation excludes repeated generators. -/
theorem source_distinct (d : Generators) (hd : IsNumericalGeneratingTuple d) :
    Function.Injective d := by
  intro i j hij
  by_contra hne
  apply hd.2.2 i
  apply AddSubmonoid.subset_closure
  exact ⟨j,Ne.symm hne,hij.symm⟩

/-- Fixed-fiber support chains, including repeated vertices, equal graph reachability. -/
theorem source_fiber_chains (d : Generators) (n : ℕ) (z w : Factorizations d n) :
    RRelated d n z w ↔ Relation.ReflTransGen
      (fun u v : Factorizations d n => (support u.val ∩ support v.val).Nonempty) z w := by
  constructor
  · intro h
    rw [RRelated, SimpleGraph.reachable_iff_reflTransGen] at h
    induction h with
    | refl => exact .refl
    | tail _ ha ih =>
      apply ih.tail
      rw [factorizationGraph, SimpleGraph.fromRel_adj] at ha
      rcases ha.2 with ⟨i,hi,hj⟩ | ⟨i,hi,hj⟩
      · exact ⟨i,hi,hj⟩
      · exact ⟨i,hj,hi⟩
  · intro h
    induction h with
    | refl => exact .rfl
    | @tail v w h ha ih =>
      by_cases he : v = w
      · subst w; exact ih
      · apply ih.trans
        apply SimpleGraph.Adj.reachable
        rw [factorizationGraph, SimpleGraph.fromRel_adj]
        obtain ⟨i,hi,hj⟩ := ha
        exact ⟨he,Or.inl ⟨i,hi,hj⟩⟩

/-- Ambient chains join any two vectors with a positive coordinate through their sum. -/
theorem source_ambient_chain (z w : Factorization) (i j : Fin 4)
    (hi : 0 < z i) (hj : 0 < w j) :
    Relation.ReflTransGen (fun u v : Factorization =>
      (support u ∩ support v).Nonempty) z w := by
  apply Relation.ReflTransGen.trans (Relation.ReflTransGen.single (b := z+w) ?_)
    (Relation.ReflTransGen.single ?_)
  · refine ⟨i,hi,?_⟩
    change 0 < z i + w i
    omega
  · refine ⟨j,?_,hj⟩
    change 0 < z j + w j
    omega

/-- Coordinate translation keeps the source's full four-dimensional fiber and support. -/
example (d : Generators) (n : ℕ) (z : Factorization) :
    z ∈ factorizations d n ↔
      z 0*d 0 + z 1*d 1 + z 2*d 2 + z 3*d 3 = n := by
  simp [factorizations,eval,Fin.sum_univ_succ]
  omega

/-- Relation witnesses retain the source minima and every allowed off-diagonal vector. -/
example (d : Generators) (m i : Fin 4) (b : ℕ) (z : Factorization) :
    IsPositiveMinimalRelation d m i b z ↔
      i ≠ m ∧ IsPositiveCriticalCoefficient d m i b ∧
        z i = 0 ∧ 0 < z m ∧ eval d z = b * d i := Iff.rfl

example (d : Generators) (i : Fin 4) (a a' : ℕ)
    (ha : IsCriticalCoefficient d i a) (ha' : IsCriticalCoefficient d i a') : a = a' :=
  ha.unique ha'

example (d : Generators) (m i : Fin 4) (b b' : ℕ)
    (hb : IsPositiveCriticalCoefficient d m i b)
    (hb' : IsPositiveCriticalCoefficient d m i b') : b = b' := hb.unique hb'

private def sourceD : Generators := ![145,203,74,111]
private def sourceA : CriticalCoefficients := ![7,5,3,2]

private theorem source_eval (z : Factorization) :
    eval sourceD z = 145*z 0 + 203*z 1 + 74*z 2 + 111*z 3 := by
  simp [eval,sourceD,Fin.sum_univ_succ]
  ring

private theorem source_fiber_left :
    factorizations sourceD 1015 = {_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure 0 7,_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure 1 5} := by
  ext z
  change eval sourceD z = 1015 ↔ z = _root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure 0 7 ∨ z = _root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure 1 5
  constructor
  · rw [source_eval]
    intro hz
    have split_degree : ∀ L R : ℕ, 29*L+37*R=1015 → L=35 ∧ R=0 := by
      intro L R h; omega
    have hh := split_degree (5*z 0+7*z 1) (2*z 2+3*z 3) (by omega)
    have h : (z 0=7 ∧ z 1=0 ∧ z 2=0 ∧ z 3=0) ∨
        (z 0=0 ∧ z 1=5 ∧ z 2=0 ∧ z 3=0) := by omega
    rcases h with h | h
    · left; funext i; fin_cases i <;> simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,h.1,h.2.1,h.2.2.1,h.2.2.2]
    · right; funext i; fin_cases i <;> simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,h.1,h.2.1,h.2.2.1,h.2.2.2]
  · rintro (rfl|rfl) <;> norm_num [pure_eval,sourceD]

private theorem source_fiber_right :
    factorizations sourceD 222 = {_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure 2 3,_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure 3 2} := by
  ext z
  change eval sourceD z = 222 ↔ z = _root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure 2 3 ∨ z = _root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure 3 2
  constructor
  · rw [source_eval]
    intro hz
    have split_degree : ∀ L R : ℕ, 29*L+37*R=222 → L=0 ∧ R=6 := by
      intro L R h; omega
    have hh := split_degree (5*z 0+7*z 1) (2*z 2+3*z 3) (by omega)
    have h : (z 0=0 ∧ z 1=0 ∧ z 2=3 ∧ z 3=0) ∨
        (z 0=0 ∧ z 1=0 ∧ z 2=0 ∧ z 3=2) := by omega
    rcases h with h | h
    · left; funext i; fin_cases i <;> simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,h.1,h.2.1,h.2.2.1,h.2.2.2]
    · right; funext i; fin_cases i <;> simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,h.1,h.2.1,h.2.2.1,h.2.2.2]
  · rintro (rfl|rfl) <;> norm_num [pure_eval,sourceD]

private theorem source_ordering : HasSecondaryOrdering sourceD sourceA := by
  refine ⟨by decide,?_,?_,?_,?_⟩
  · simpa [sourceD,sourceA] using source_fiber_left
  · simpa [sourceD,sourceA] using source_fiber_left
  · simpa [sourceD,sourceA] using source_fiber_right
  · simpa [sourceD,sourceA] using source_fiber_right

private theorem critical_from_fiber (d : Generators) (i j : Fin 4) (hij : i ≠ j)
    (A B : ℕ) (hA : 0 < A)
    (hf : factorizations d (A*d i) = {pure i A,pure j B}) : IsCriticalCoefficient d i A := by
  classical
  have hB : eval d (pure j B) = A*d i := by
    have hh : pure j B ∈ factorizations d (A*d i) := by rw [hf]; simp
    exact hh
  refine ⟨⟨hA,pure j B,by simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,hij],hB⟩,?_⟩
  rintro k ⟨hk,z,hzi,hz⟩
  by_contra hnot
  have hka : k ≤ A := by omega
  let w := z + pure i (A-k)
  have hw : w ∈ factorizations d (A*d i) := by
    change eval d w = A*d i
    have hs := congrArg (· * d i) (Nat.sub_add_cancel hka)
    simp only [Nat.add_mul] at hs
    simp only [w,eval,Pi.add_apply,add_mul,Finset.sum_add_distrib] at *
    have hp := pure_eval d i (A-k)
    unfold eval at hp
    omega
  rw [hf] at hw
  rcases hw with he | he
  · have hh := congrFun he i
    simp [w,_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,hzi] at hh
    omega
  · have hh := congrFun he i
    simp [w,_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,hzi,hij] at hh
    omega

private theorem source_critical : IsCriticalData sourceD sourceA := by
  intro i
  fin_cases i
  · exact critical_from_fiber sourceD 0 1 (by decide) 7 5 (by decide) source_fiber_left
  · exact critical_from_fiber sourceD 1 0 (by decide) 5 7 (by decide)
      (by simpa [Set.pair_comm,sourceD] using source_fiber_left)
  · exact critical_from_fiber sourceD 2 3 (by decide) 3 2 (by decide) source_fiber_right
  · exact critical_from_fiber sourceD 3 2 (by decide) 2 3 (by decide)
      (by simpa [Set.pair_comm,sourceD] using source_fiber_right)

private theorem source_numerical : IsNumericalGeneratingTuple sourceD := by
  refine ⟨?_,by decide,?_⟩
  · intro i; fin_cases i <;> decide
  · intro i hn
    obtain ⟨z,hzi,hz⟩ := (source_excluded_generator sourceD i _).mp hn
    have hle : sourceA i ≤ 1 := (source_critical i).2 ⟨by decide,z,hzi,by simpa using hz⟩
    fin_cases i <;> norm_num [sourceA] at hle

/-- A kernel check of the source's displayed secondary example, on the full domain. -/
theorem source_domain_nonempty : ∃ d a b, IsOrderedSecondary d a b := by
  obtain ⟨a,b,ha,hb⟩ := result.1 sourceD source_numerical
  have hae : a = sourceA := by
    funext i
    exact (ha i).unique (source_critical i)
  subst a
  refine ⟨sourceD,sourceA,b,source_numerical,source_critical,hb,?_,source_ordering⟩
  rintro ⟨m,i,j,him,hjm,hij,hi,hj⟩
  have hmate : ∀ k : Fin 4, k ≠ m → sourceA k = b m k →
      m = (![1,0,3,2] : Fin 4 → Fin 4) k := by
    intro k hkm heq
    obtain ⟨z,hzk,hzm,hz⟩ := (hb.2 m k hkm).1.2
    rw [← heq] at hz
    have hm : z ∈ factorizations sourceD (sourceA k * sourceD k) := hz
    fin_cases k
    · change m = 1
      change z ∈ factorizations sourceD 1015 at hm
      rw [source_fiber_left] at hm
      rcases hm with rfl | rfl
      · simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure] at hzk
      · by_contra h; simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,h] at hzm
    · change m = 0
      change z ∈ factorizations sourceD 1015 at hm
      rw [source_fiber_left] at hm
      rcases hm with rfl | rfl
      · by_contra h; simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,h] at hzm
      · simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure] at hzk
    · change m = 3
      change z ∈ factorizations sourceD 222 at hm
      rw [source_fiber_right] at hm
      rcases hm with rfl | rfl
      · simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure] at hzk
      · by_contra h; simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,h] at hzm
    · change m = 2
      change z ∈ factorizations sourceD 222 at hm
      rw [source_fiber_right] at hm
      rcases hm with rfl | rfl
      · by_contra h; simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure,h] at hzm
      · simp [_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.pure] at hzk
  have hmi := hmate i him hi
  have hmj := hmate j hjm hj
  have hinj : Function.Injective (![1,0,3,2] : Fin 4 → Fin 4) := by decide
  exact hij (hinj (hmi.symm.trans hmj))

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-! The following source reconstructions are conditional audit attempts. Variation,
sensitivity, and observational dependence are explicit unsupplied proof arguments;
there is no closed four-slot registration. Raw occurrence selection is unspecified. -/

namespace Minimum

abbrev scope := type_of% (@_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.positive_minimum_excludes_coordinate)

abbrev signature : Signature where
  Params := Fin 4
  State _ := Factorization
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ i z => z i) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : Generators) (hd : ∀ j, 0 < d j) (m i : Fin 4) (hi : i ≠ m)
      (b : ℕ) (hb : IsPositiveCriticalCoefficient d m i b) (z : Factorization)
      (hz : eval d z = b*d i) (hm : 0 < z m), R.readout () i z = 0

theorem source_bridge : scope ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual :=
  _root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.positive_minimum_excludes_coordinate

def family (variation : Variation arena actual) (sensitivity : Sensitivity arena actual)
    (dependence : ObservationalDependence signature actual) : Registration arena scope where
  actual := actual
  bridge := source_bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

end Minimum

namespace PositivePair

abbrev scope := type_of% (@_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.critical_pair_positive_representation)

abbrev signature : Signature where
  Params := Generators × Fin 4 × Fin 4
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ p z => z.1*p.1 p.2.1 + z.2*p.1 p.2.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : Generators) (hd : ∀ i, 0 < d i) (x y c : Fin 4)
      (hxy : x ≠ y) (hcx : c ≠ x) (hcy : c ≠ y) (A B : ℕ)
      (hA : IsCriticalCoefficient d x A)
      (hf : factorizations d (A*d x) = {pure x A,pure y B}),
      ∃ α β : ℕ, 0 < α ∧ 0 < β ∧
        (Nat.gcd (d x) (d y) / Nat.gcd (Nat.gcd (d x) (d y)) (d c))*d c =
          R.readout () (d,x,y) (α,β)

theorem source_bridge : scope ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual :=
  _root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.critical_pair_positive_representation

def family (variation : Variation arena actual) (sensitivity : Sensitivity arena actual)
    (dependence : ObservationalDependence signature actual) : Registration arena scope where
  actual := actual
  bridge := source_bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

end PositivePair

namespace Bounds

abbrev scope := type_of% (@_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.secondary_boundary_bounds)

abbrev signature : Signature where
  Params := PositiveCriticalCoefficients
  State _ := Fin 4
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ b i => boundaryCoefficient b i) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : Generators) (a : CriticalCoefficients) (b : PositiveCriticalCoefficients)
      (hs : IsOrderedSecondary d a b) (i : Fin 4) (hi : i=2 ∨ i=3),
      a i < R.readout () b i ∧ R.readout () b i ≤
        Nat.gcd (d 0) (d 1) / Nat.gcd (Nat.gcd (d 0) (d 1)) (d i)

theorem source_bridge : scope ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual :=
  _root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.secondary_boundary_bounds

def family (variation : Variation arena actual) (sensitivity : Sensitivity arena actual)
    (dependence : ObservationalDependence signature actual) : Registration arena scope where
  actual := actual
  bridge := source_bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

end Bounds

namespace Mixed

abbrev scope := type_of% (@_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.equality_excludes_mixed)

abbrev signature : Signature where
  Params := Unit
  State _ := Factorization
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Factorization
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ z => z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d : Generators) (a : CriticalCoefficients) (b : PositiveCriticalCoefficients)
      (hs : IsOrderedSecondary d a b) (i : Fin 4) (hi : i=2 ∨ i=3)
      (heq : b 0 i = Nat.gcd (d 0) (d 1) / Nat.gcd (Nat.gcd (d 0) (d 1)) (d i))
      (z : Factorization) (hz : eval d z = b 0 i*d i),
      (R.readout () () z 0=0 ∧ R.readout () () z 1=0) ∨
        (R.readout () () z 2=0 ∧ R.readout () () z 3=0)

theorem source_bridge : scope ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual :=
  _root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.equality_excludes_mixed

def family (variation : Variation arena actual) (sensitivity : Sensitivity arena actual)
    (dependence : ObservationalDependence signature actual) : Registration arena scope where
  actual := actual
  bridge := source_bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

end Mixed

namespace Boundary

abbrev scope := type_of% (@_root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.result)

abbrev signature : Signature where
  Params := Generators
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ d n => n ∈ Betti d) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := (∀ d : Generators, IsNumericalGeneratingTuple d →
      ∃ (a : CriticalCoefficients) (b : PositiveCriticalCoefficients),
        IsCriticalData d a ∧ IsPositiveCriticalData d b) ∧
      ∀ (d : Generators) (a : CriticalCoefficients) (b : PositiveCriticalCoefficients),
        IsOrderedSecondary d a b → ∀ i : Fin 4, (i=2 ∨ i=3) →
        let p := Nat.gcd (d 0) (d 1)
        let r := p / Nat.gcd p (d i)
        let n := boundaryCoefficient b i*d i
        (R.readout () d n ↔ boundaryCoefficient b i=r) ∧
        (boundaryCoefficient b i=r → HasExactlyPairComponents d n) ∧
        (boundaryCoefficient b i≠r → (factorizationGraph d n).Connected)

theorem source_bridge : scope ↔ arena.Law actual := Iff.rfl

theorem actual_law : arena.Law actual :=
  _root_.D5.NumberTheory.NumericalSemigroups.SecondaryBoundaryBetti.result

def family (variation : Variation arena actual) (sensitivity : Sensitivity arena actual)
    (dependence : ObservationalDependence signature actual) : Registration arena scope where
  actual := actual
  bridge := source_bridge
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

end Boundary

end Reg.D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti

#print axioms Reg.D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti.source_semigroup
#print axioms Reg.D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti.source_excluded_generator
#print axioms Reg.D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti.source_set_gcd
#print axioms Reg.D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti.source_cofinite
#print axioms Reg.D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti.source_distinct
#print axioms Reg.D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti.source_fiber_chains
#print axioms Reg.D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti.source_ambient_chain
#print axioms Reg.D5.S3.Arith.NumericalSemigroups.SecondaryBoundaryBetti.source_domain_nonempty
