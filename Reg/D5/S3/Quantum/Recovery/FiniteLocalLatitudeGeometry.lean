import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
import Reg.Support.DependentFamily

open D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := ⟨{()}, by intro x; cases x; simp⟩
  nonemptyRole := ⟨()⟩
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := ⟨∅, by intro e; exact nomatch e⟩

def actual : Realization signature :=
  realize signature (fun _ _ r => h r) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (r : ℝ) (hr : 0 < r) (hlo : 1/2 < r^2) (hhi : r^2 < 2),
    ((∃ b : Fin 3 → ℂ, Normalized b ∧ Flat r b) ∧
    (∀ b : Fin 3 → ℂ, Normalized b → Flat r b →
      (∀ i, response r b i = 1/3) ∧
      (∀ k, Complex.normSq (b k) = 1/3) ∧
      ‖b 1^2 - 2*b 0*b 2‖ = kappa r)) ∧
    (∃ x y : Fin 2 → ℂ, UnitSpinor x ∧ UnitSpinor y ∧ ∀ i, productResponse r x y i = R.readout () () r) ∧
    (∀ x y : Fin 2 → ℂ, UnitSpinor x → UnitSpinor y → FlatProduct r x y →
      (∀ i, productResponse r x y i = h r) ∧ antisymmetricWeight x y = g r ∧
      spinorZ x = -spinorZ y ∧ (spinorZ x)^2 = 1-4*h r) ∧
    (K_s r).Nonempty ∧
    (∀ a b : Bloch, (a,b) ∈ K_s r →
      a 2 = -b 2 ∧ (a 2)^2 = 1-4*h r ∧ defect a b = g r)

theorem actual_law : arena.Law actual := all_r_flat_geometry

theorem rejected_law : ¬ arena.Law rejected := by
  intro bad
  obtain ⟨_,⟨x,y,hx,hy,flat⟩,_⟩ := bad 1 (by norm_num) (by norm_num) (by norm_num)
  have hf : FlatProduct 1 x y := by
    intro i
    exact (flat i).trans (flat 0).symm
  have geom := (all_r_flat_geometry 1 (by norm_num) (by norm_num) (by norm_num)).2.2.1 x y hx hy hf
  have eq := (geom.1 0).symm.trans (flat 0)
  have hp : 0 < h 1 := by unfold h kappa; positivity
  exact (ne_of_gt hp) eq

def registration : Registration arena (∀ (r : ℝ) (hr : 0 < r)
    (hlo : 1/2 < r^2) (hhi : r^2 < 2),
    ((∃ b : Fin 3 → ℂ, Normalized b ∧ Flat r b) ∧
    (∀ b : Fin 3 → ℂ, Normalized b → Flat r b →
      (∀ i, response r b i = 1/3) ∧
      (∀ k, Complex.normSq (b k) = 1/3) ∧
      ‖b 1^2 - 2*b 0*b 2‖ = kappa r)) ∧
    (∃ x y : Fin 2 → ℂ, UnitSpinor x ∧ UnitSpinor y ∧ ∀ i, productResponse r x y i = h r) ∧
    (∀ x y : Fin 2 → ℂ, UnitSpinor x → UnitSpinor y → FlatProduct r x y →
      (∀ i, productResponse r x y i = h r) ∧ antisymmetricWeight x y = g r ∧
      spinorZ x = -spinorZ y ∧ (spinorZ x)^2 = 1-4*h r) ∧
    (K_s r).Nonempty ∧
    (∀ a b : Bloch, (a,b) ∈ K_s r →
      a 2 = -b 2 ∧ (a 2)^2 = 1-4*h r ∧ defect a b = g r)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e; exact nomatch e
  dependence := by
    intro i
    refine ⟨(),(0:ℝ),(1:ℝ),?_⟩
    change h 0 ≠ h 1
    intro heq
    have h0 : kappa 0 = 2/3 := by norm_num [kappa]
    have kp : 0 < 1+kappa 1 := by unfold kappa; positivity
    have hks : (kappa 1)^2 = 8/9 := by
      unfold kappa
      rw [div_pow,Real.sq_sqrt (by norm_num)]
      norm_num
    unfold h at heq
    rw [h0] at heq
    have kk : kappa 1 = 2/3 := by
      field_simp [ne_of_gt kp] at heq
      linarith
    rw [kk] at hks
    norm_num at hks

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.all_r_flat_geometry) (type_of% (realize.{0, 0, 0, 0, 0} signature (fun _ _ r => h r) (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Quantum") "Recovery") "FiniteLocalLatitudeGeometry") "all_r_flat_geometry") "Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry/Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature (fun _ _ r => h r) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "arg", "fn", "arg", "arg", "body", "arg", "body", "arg", "arg", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.all_r_flat_geometry, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.canonicalArenaFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.sourceBridgeFact, `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.observationFact0, `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.anchorEnumeration }


#print axioms registration
end Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry


noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.arena
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.arena
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.arena
    (∀ (r : Real)
      (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
      (hlo :
        @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (hhi :
        @LT.lt.{0} Real Real.instLT
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))),
      And
        (And
          (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Complex)
            fun (b : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Complex) =>
            And (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Normalized b)
              (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Flat r b))
          (∀ (b : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Complex),
            D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Normalized b →
              D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Flat r b →
                And
                  (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
                    @Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.response r b i)
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@OfNat.ofNat.{0} Real (nat_lit 3)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  (And
                    (∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
                      @Eq.{1} Real
                        (@DFunLike.coe.{1, 1, 1}
                          (@MonoidWithZeroHom.{0, 0} Complex Real
                            (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)
                            (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring))
                          Complex (fun (x : Complex) => Real)
                          (@MonoidWithZeroHom.funLike.{0, 0} Complex Real
                            (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)
                            (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring))
                          Complex.normSq (b k))
                        (@HDiv.hDiv.{0, 0, 0} Real Real Real
                          (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                          (@OfNat.ofNat.{0} Real (nat_lit 3)
                            (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                    (@Eq.{1} Real
                      (@Norm.norm.{0} Complex Complex.instNorm
                        (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                          (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                            (@instHPow.{0, 0} Complex Nat
                              (@NPow.toPow.{0} Complex
                                (@Monoid.toNPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                            (b
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 1)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 1))))
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                            (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                              (@OfNat.ofNat.{0} Complex (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                              (b
                                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  (nat_lit 0)
                                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (nat_lit 0)))))
                            (b
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 2)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 2)))))))
                      (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.kappa r)))))
        (And
          (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex)
            fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex) =>
            @Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex)
              fun (y : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex) =>
              And (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor x)
                (And (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor y)
                  (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
                    @Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.productResponse r x y i)
                      (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.h r))))
          (And
            (∀ (x y : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex),
              D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor x →
                D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor y →
                  D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.FlatProduct r x y →
                    And
                      (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
                        @Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.productResponse r x y i)
                          (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.h r))
                      (And
                        (@Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.antisymmetricWeight x y)
                          (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.g r))
                        (And
                          (@Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.spinorZ x)
                            (@Neg.neg.{0} Real Real.instNeg
                              (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.spinorZ y)))
                          (@Eq.{1} Real
                            (@HPow.hPow.{0, 0, 0} Real Nat Real
                              (@instHPow.{0, 0} Real Nat
                                (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                              (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.spinorZ x)
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                              (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 4)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.h r)))))))
            (And
              (@Set.Nonempty.{0}
                (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                  D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.K_s r))
              (∀ (a b : D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch),
                @Membership.mem.{0, 0}
                    (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                      D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                    (Set.{0}
                      (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                        D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch))
                    (@Set.instMembership.{0}
                      (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                        D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch))
                    (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.K_s r)
                    (@Prod.mk.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                      D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch a b) →
                  And
                    (@Eq.{1}
                      ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 2)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (nat_lit 2))))
                      (@WithLp.ofLp.{0}
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            PiLp.innerProductSpace._proof_1))
                        ((i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                          (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real) i)
                        a
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 2)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (nat_lit 2))))
                      (@Neg.neg.{0}
                        ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 2)
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (nat_lit 2))))
                        Real.instNeg
                        (@WithLp.ofLp.{0}
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                              PiLp.innerProductSpace._proof_1))
                          ((i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                            (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real) i)
                          b
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 2)
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (nat_lit 2))))))
                    (And
                      (@Eq.{1}
                        ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 2)
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (nat_lit 2))))
                        (@HPow.hPow.{0, 0, 0}
                          ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          Nat
                          ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          (@instHPow.{0, 0}
                            ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 2)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 2))))
                            Nat
                            (@NPow.toPow.{0}
                              ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  (nat_lit 2)
                                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (nat_lit 2))))
                              (@Monoid.toNPow.{0}
                                ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                    (nat_lit 2)
                                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (nat_lit 2))))
                                Real.instMonoid)))
                          (@WithLp.ofLp.{0}
                            (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                                (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                  (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal
                                    ENNReal.instAddCommMonoidWithOne))
                                PiLp.innerProductSpace._proof_1))
                            ((i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                              (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real) i)
                            a
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@HSub.hSub.{0, 0, 0}
                          ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          (@instHSub.{0}
                            ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 2)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 2))))
                            Real.instSub)
                          (@OfNat.ofNat.{0}
                            ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 2)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 2))))
                            (nat_lit 1)
                            (@One.toOfNat1.{0}
                              ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  (nat_lit 2)
                                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (nat_lit 2))))
                              Real.instOne))
                          (@HMul.hMul.{0, 0, 0}
                            ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 2)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 2))))
                            Real
                            ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 2)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 2))))
                            (@instHMul.{0}
                              ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  (nat_lit 2)
                                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (nat_lit 2))))
                              Real.instMul)
                            (@OfNat.ofNat.{0}
                              ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  (nat_lit 2)
                                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (nat_lit 2))))
                              (nat_lit 4)
                              (@instOfNatAtLeastTwo.{0}
                                ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                                  (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                    (nat_lit 2)
                                    (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (nat_lit 2))))
                                (nat_lit 4) Real.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                            (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.h r))))
                      (@Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.defect a b)
                        (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.g r))))))))
    Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration)

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"all_r_flat_geometry\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.all_r_flat_geometry, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.arena
  (∀ (r : Real)
    (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
    (hlo :
      @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hhi :
      @LT.lt.{0} Real Real.instLT
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))),
    And
      (And
        (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Complex)
          fun (b : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Complex) =>
          And (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Normalized b)
            (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Flat r b))
        (∀ (b : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) → Complex),
          D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Normalized b →
            D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Flat r b →
              And
                (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
                  @Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.response r b i)
                    (@HDiv.hDiv.{0, 0, 0} Real Real Real
                      (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                      (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                      (@OfNat.ofNat.{0} Real (nat_lit 3)
                        (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                (And
                  (∀ (k : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
                    @Eq.{1} Real
                      (@DFunLike.coe.{1, 1, 1}
                        (@MonoidWithZeroHom.{0, 0} Complex Real
                          (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)
                          (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring))
                        Complex (fun (x : Complex) => Real)
                        (@MonoidWithZeroHom.funLike.{0, 0} Complex Real
                          (@instMulZeroOneClassOfSemiring.{0} Complex Complex.instSemiring)
                          (@instMulZeroOneClassOfSemiring.{0} Real Real.semiring))
                        Complex.normSq (b k))
                      (@HDiv.hDiv.{0, 0, 0} Real Real Real
                        (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
                        (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                        (@OfNat.ofNat.{0} Real (nat_lit 3)
                          (@instOfNatAtLeastTwo.{0} Real (nat_lit 3) Real.instNatCast
                            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))))))
                  (@Eq.{1} Real
                    (@Norm.norm.{0} Complex Complex.instNorm
                      (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                        (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                          (@instHPow.{0, 0} Complex Nat
                            (@NPow.toPow.{0} Complex
                              (@Monoid.toNPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                          (b
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 1)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 1))))
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                          (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                            (@OfNat.ofNat.{0} Complex (nat_lit 2)
                              (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
                                (@Nat.instAtLeastTwoHAddOfNat
                                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                            (b
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 0)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 0)))))
                          (b
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2)))))))
                    (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.kappa r)))))
      (And
        (@Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex)
          fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex) =>
          @Exists.{1} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex)
            fun (y : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex) =>
            And (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor x)
              (And (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor y)
                (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
                  @Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.productResponse r x y i)
                    (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.h r))))
        (And
          (∀ (x y : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex),
            D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor x →
              D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.UnitSpinor y →
                D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.FlatProduct r x y →
                  And
                    (∀ (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))),
                      @Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.productResponse r x y i)
                        (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.h r))
                    (And
                      (@Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.antisymmetricWeight x y)
                        (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.g r))
                      (And
                        (@Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.spinorZ x)
                          (@Neg.neg.{0} Real Real.instNeg
                            (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.spinorZ y)))
                        (@Eq.{1} Real
                          (@HPow.hPow.{0, 0, 0} Real Nat Real
                            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                            (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.spinorZ x)
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                              (@OfNat.ofNat.{0} Real (nat_lit 4)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                              (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.h r)))))))
          (And
            (@Set.Nonempty.{0}
              (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
              (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.K_s r))
            (∀ (a b : D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch),
              @Membership.mem.{0, 0}
                  (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                    D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch)
                  (Set.{0}
                    (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                      D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch))
                  (@Set.instMembership.{0}
                    (Prod.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                      D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch))
                  (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.K_s r)
                  (@Prod.mk.{0, 0} D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch
                    D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.Bloch a b) →
                And
                  (@Eq.{1}
                    ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (nat_lit 2))))
                    (@WithLp.ofLp.{0}
                      (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                          (@AddMonoidWithOne.toNatCast.{0} ENNReal
                            (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                          PiLp.innerProductSpace._proof_1))
                      ((i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                        (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real) i)
                      a
                      (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) (nat_lit 2)
                        (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (nat_lit 2))))
                    (@Neg.neg.{0}
                      ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 2)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (nat_lit 2))))
                      Real.instNeg
                      (@WithLp.ofLp.{0}
                        (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                          (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                            (@AddMonoidWithOne.toNatCast.{0} ENNReal
                              (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                            PiLp.innerProductSpace._proof_1))
                        ((i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                          (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real) i)
                        b
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 2)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (nat_lit 2))))))
                  (And
                    (@Eq.{1}
                      ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                        (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                          (nat_lit 2)
                          (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (nat_lit 2))))
                      (@HPow.hPow.{0, 0, 0}
                        ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 2)
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (nat_lit 2))))
                        Nat
                        ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 2)
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (nat_lit 2))))
                        (@instHPow.{0, 0}
                          ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          Nat
                          (@NPow.toPow.{0}
                            ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 2)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 2))))
                            (@Monoid.toNPow.{0}
                              ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  (nat_lit 2)
                                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (nat_lit 2))))
                              Real.instMonoid)))
                        (@WithLp.ofLp.{0}
                          (@OfNat.ofNat.{0} ENNReal (nat_lit 2)
                            (@instOfNatAtLeastTwo.{0} ENNReal (nat_lit 2)
                              (@AddMonoidWithOne.toNatCast.{0} ENNReal
                                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0} ENNReal ENNReal.instAddCommMonoidWithOne))
                              PiLp.innerProductSpace._proof_1))
                          ((i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) →
                            (fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real) i)
                          a
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 2)
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (nat_lit 2))))
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@HSub.hSub.{0, 0, 0}
                        ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 2)
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (nat_lit 2))))
                        ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 2)
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (nat_lit 2))))
                        ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                          (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                            (nat_lit 2)
                            (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (nat_lit 2))))
                        (@instHSub.{0}
                          ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          Real.instSub)
                        (@OfNat.ofNat.{0}
                          ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          (nat_lit 1)
                          (@One.toOfNat1.{0}
                            ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 2)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 2))))
                            Real.instOne))
                        (@HMul.hMul.{0, 0, 0}
                          ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          Real
                          ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                            (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                              (nat_lit 2)
                              (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (nat_lit 2))))
                          (@instHMul.{0}
                            ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 2)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 2))))
                            Real.instMul)
                          (@OfNat.ofNat.{0}
                            ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                              (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                (nat_lit 2)
                                (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (nat_lit 2))))
                            (nat_lit 4)
                            (@instOfNatAtLeastTwo.{0}
                              ((fun (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))) => Real)
                                (@OfNat.ofNat.{0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                                  (nat_lit 2)
                                  (@Fin.instOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (nat_lit 2))))
                              (nat_lit 4) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat
                                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                          (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.h r))))
                    (@Eq.{1} Real (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.defect a b)
                      (D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.g r))))))))
  Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration)

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [Unit.unit]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.observation0 : (r : Real) →
  (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r) →
    (hlo :
        @LT.lt.{0} Real Real.instLT
          (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      (hhi :
          @LT.lt.{0} Real Real.instLT
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Real (nat_lit 2)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))) →
        (x y : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex) →
          (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) →
            D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
              Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.signature Unit.unit PUnit.unit.{1} :=
  fun (r : Real)
    (hr : @LT.lt.{0} Real Real.instLT (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) r)
    (hlo :
      @LT.lt.{0} Real Real.instLT
        (@HDiv.hDiv.{0, 0, 0} Real Real Real (@instHDiv.{0} Real (@DivInvMonoid.toDiv.{0} Real Real.instDivInvMonoid))
          (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
          (@OfNat.ofNat.{0} Real (nat_lit 2)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
    (hhi :
      @LT.lt.{0} Real Real.instLT
        (@HPow.hPow.{0, 0, 0} Real Nat Real
          (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid))) r
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (@OfNat.ofNat.{0} Real (nat_lit 2)
          (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
            (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
              (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
    (x y : Fin (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) → Complex)
    (i : Fin (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.signature
    Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.actual Unit.unit PUnit.unit.{1} r

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"all_r_flat_geometry\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"argument\",\"function\",\"argument\",\"argument\",\"body\",\"argument\",\"body\",\"argument\",\"argument\",\"body\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.all_r_flat_geometry, part := .type, path := [.body, .body, .body, .body, .argument, .function, .argument, .argument, .body, .argument, .body, .argument, .argument, .body, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"all_r_flat_geometry\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.all_r_flat_geometry, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration).actual (Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration).variation.2.choose (Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration).variation.1 (Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Quantum\",\"Recovery\",\"FiniteLocalLatitudeGeometry\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry, declaration := `Reg.D5.S3.Quantum.Recovery.FiniteLocalLatitudeGeometry.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
