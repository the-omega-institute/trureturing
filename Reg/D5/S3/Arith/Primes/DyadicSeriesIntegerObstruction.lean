import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction

open _root_.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := ℕ → ℂ
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ s j => (2 : ℂ) ^ (j + padicValNat 2 j.factorial) * s j)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law a := ∀ (s : ℕ → ℂ) (r : ℕ) (_hr : 1 ≤ r) (x : ℤ) (_hx : 2 < x)
    (μ : ℂ) (_hs0 : s 0 = 1)
    (_hscaled : ∀ j : ℕ, 0 < j → ∃ z : ℤ, Odd z ∧ a.readout () s j = (z : ℂ))
    (_hsupper : ∀ j : ℕ, ‖s j‖ ≤ (Real.sqrt (2 : ℝ)) ^ r * (4 : ℝ) ^ j)
    (_hsum : HasSum (fun j : ℕ => s j * (((x : ℂ) ^ 2)⁻¹) ^ j) μ)
    (_hgap : 128 * (6 : ℝ) ^ r < (x : ℝ) ^ 2 - 4),
    ∀ M : ℤ, (x : ℂ) ^ r * μ ≠ (M : ℂ)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let s : ℕ → ℂ := fun j => if j = 0 then 1 else 0
  have hs0 : s 0 = 1 := by simp [s]
  have hscale : ∀ j : ℕ, 0 < j → ∃ z : ℤ, Odd z ∧ rejected.readout () s j = (z : ℂ) := by
    intro j hj
    exact ⟨1, by norm_num, by simp [rejected, realize]⟩
  have hroot : 1 ≤ Real.sqrt (2 : ℝ) := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hpos := Real.sqrt_nonneg (2 : ℝ)
    nlinarith
  have hupper : ∀ j : ℕ, ‖s j‖ ≤ (Real.sqrt (2 : ℝ)) ^ 1 * (4 : ℝ) ^ j := by
    intro j
    by_cases hj : j = 0
    · subst j
      simpa [s] using hroot
    · simp only [s, if_neg hj, norm_zero, pow_one]
      positivity
  have hsum : HasSum (fun j : ℕ => s j * (((100 : ℤ) : ℂ) ^ 2)⁻¹ ^ j) (1 : ℂ) := by
    convert hasSum_ite_eq (0 : ℕ) (1 : ℂ) using 1
    ext j
    by_cases hj : j = 0 <;> simp [s, hj]
  have hbad := h s 1 (by norm_num) 100 (by norm_num) 1 hs0 hscale hupper hsum
    (by norm_num) 100
  norm_num at hbad

def registration : Registration arena
    (∀ (s : ℕ → ℂ) (r : ℕ) (_hr : 1 ≤ r) (x : ℤ) (_hx : 2 < x)
      (μ : ℂ) (_hs0 : s 0 = 1)
      (_hscaled : ∀ j : ℕ, 0 < j → ∃ z : ℤ, Odd z ∧
        (2 : ℂ) ^ (j + padicValNat 2 j.factorial) * s j = (z : ℂ))
      (_hsupper : ∀ j : ℕ, ‖s j‖ ≤ (Real.sqrt (2 : ℝ)) ^ r * (4 : ℝ) ^ j)
      (_hsum : HasSum (fun j : ℕ => s j * (((x : ℂ) ^ 2)⁻¹) ^ j) μ)
      (_hgap : 128 * (6 : ℝ) ^ r < (x : ℝ) ^ 2 - 4),
      ∀ M : ℤ, (x : ℂ) ^ r * μ ≠ (M : ℂ)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨dyadic_series_integer_obstruction, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    change ObservationalDependence signature actual
    intro i
    refine ⟨(fun _ => (1 : ℂ)), 0, 1, ?_⟩
    change (2 : ℂ) ^ (0 + padicValNat 2 (0 : ℕ).factorial) * 1 ≠
      (2 : ℂ) ^ (1 + padicValNat 2 (1 : ℕ).factorial) * 1
    norm_num

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@_root_.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.dyadic_series_integer_obstruction) (type_of% (realize.{0, 0, 0, 0, 0} signature
    (fun _ s j => (2 : ℂ) ^ (j + padicValNat 2 j.factorial) * s j)
    (fun e => nomatch e))) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Arith") "Primes") "DyadicSeriesIntegerObstruction") "dyadic_series_integer_obstruction") "Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction/Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.arena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨(arena)⟩,
  objectArena := .source ⟨(arena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena) ⟨(registration)⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0, 0, 0, 0, 0} signature
    (fun _ s j => (2 : ℂ) ^ (j + padicValNat 2 j.factorial) * s j)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "arg", "body", "arg", "fn", "arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.dyadic_series_integer_obstruction, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.canonicalArenaFact, `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.canonicalObjectArenaFact, `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.sourceBridgeFact, `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.observationFact0, `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.descriptorFact] },
  exclusion := some `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.statementExclusion,
  finiteLift := none,
  roleEnumeration := some `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.roleEnumeration,
  anchorEnumeration := some `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.anchorEnumeration }


end Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction


noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.arena
noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.{0, 0, 0, 0, 0} :=
  Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.arena
noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence


noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.sourceLaw : Prop :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.arena
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.actual.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.arena
    (∀ (s : Nat → Complex) (r : Nat)
      (_hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r) (x : Int)
      (_hx : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) x) (μ : Complex)
      (_hs0 :
        @Eq.{1} Complex (s (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
      (_hscaled :
        ∀ (j : Nat),
          @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
            @Exists.{1} Int fun (z : Int) =>
              And (@Odd.{0} Int Int.instSemiring z)
                (@Eq.{1} Complex
                  (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                    (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                      (@instHPow.{0, 0} Complex Nat
                        (@NPow.toPow.{0} Complex
                          (@Monoid.toNPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                      (@OfNat.ofNat.{0} Complex (nat_lit 2)
                        (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
                          (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                        (padicValNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Nat.factorial j))))
                    (s j))
                  (@Int.cast.{0} Complex Complex.instIntCast z)))
      (_hsupper :
        ∀ (j : Nat),
          @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (s j))
            (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (Real.sqrt
                  (@OfNat.ofNat.{0} Real (nat_lit 2)
                    (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
                r)
              (@HPow.hPow.{0, 0, 0} Real Nat Real
                (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
                (@OfNat.ofNat.{0} Real (nat_lit 4)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                j)))
      (_hsum :
        @HasSum.{0, 0} Complex Nat Complex.instAddCommMonoid
          (@UniformSpace.toTopologicalSpace.{0} Complex
            (@PseudoMetricSpace.toUniformSpace.{0} Complex
              (@SeminormedRing.toPseudoMetricSpace.{0} Complex
                (@SeminormedCommRing.toSeminormedRing.{0} Complex
                  (@NormedCommRing.toSeminormedCommRing.{0} Complex
                    (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
          (fun (j : Nat) =>
            @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (s j)
              (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                (@instHPow.{0, 0} Complex Nat
                  (@NPow.toPow.{0} Complex
                    (@Monoid.toNPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                (@Inv.inv.{0} Complex Complex.instInv
                  (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                    (@instHPow.{0, 0} Complex Nat
                      (@NPow.toPow.{0} Complex
                        (@Monoid.toNPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                    (@Int.cast.{0} Complex Complex.instIntCast x)
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                j))
          μ (SummationFilter.unconditional.{0} Nat))
      (_hgap :
        @LT.lt.{0} Real Real.instLT
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@OfNat.ofNat.{0} Real (nat_lit 128)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 6)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
              r))
          (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@Int.cast.{0} Real Real.instIntCast x) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@OfNat.ofNat.{0} Real (nat_lit 4)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
      (M : Int),
      @Ne.{1} Complex
        (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
          (@HPow.hPow.{0, 0, 0} Complex Nat Complex
            (@instHPow.{0, 0} Complex Nat
              (@NPow.toPow.{0} Complex
                (@Monoid.toNPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
            (@Int.cast.{0} Complex Complex.instIntCast x) r)
          μ)
        (@Int.cast.{0} Complex Complex.instIntCast M))
    Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration)

noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.sourceBridgeFact : LeanInformationAudit.Contract.NodeFact := .equivalent
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"dyadic_series_integer_obstruction\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"registration_1\",\"sourceLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.dyadic_series_integer_obstruction, part := .type, path := [], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.sourceLaw, part := .value, path := [], levels := [] }
  (@D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Registration.bridge.{0, 0, 0, 0, 0}
  Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.arena
  (∀ (s : Nat → Complex) (r : Nat)
    (_hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r) (x : Int)
    (_hx : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) x) (μ : Complex)
    (_hs0 :
      @Eq.{1} Complex (s (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
    (_hscaled :
      ∀ (j : Nat),
        @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
          @Exists.{1} Int fun (z : Int) =>
            And (@Odd.{0} Int Int.instSemiring z)
              (@Eq.{1} Complex
                (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
                  (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                    (@instHPow.{0, 0} Complex Nat
                      (@NPow.toPow.{0} Complex
                        (@Monoid.toNPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                    (@OfNat.ofNat.{0} Complex (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Complex (nat_lit 2) Complex.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) j
                      (padicValNat (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (Nat.factorial j))))
                  (s j))
                (@Int.cast.{0} Complex Complex.instIntCast z)))
    (_hsupper :
      ∀ (j : Nat),
        @LE.le.{0} Real Real.instLE (@Norm.norm.{0} Complex Complex.instNorm (s j))
          (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (Real.sqrt
                (@OfNat.ofNat.{0} Real (nat_lit 2)
                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                    (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                      (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))))
              r)
            (@HPow.hPow.{0, 0, 0} Real Nat Real
              (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
              (@OfNat.ofNat.{0} Real (nat_lit 4)
                (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
                  (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                    (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
              j)))
    (_hsum :
      @HasSum.{0, 0} Complex Nat Complex.instAddCommMonoid
        (@UniformSpace.toTopologicalSpace.{0} Complex
          (@PseudoMetricSpace.toUniformSpace.{0} Complex
            (@SeminormedRing.toPseudoMetricSpace.{0} Complex
              (@SeminormedCommRing.toSeminormedRing.{0} Complex
                (@NormedCommRing.toSeminormedCommRing.{0} Complex
                  (@CommCStarAlgebra.toNormedCommRing.{0} Complex instCommCStarAlgebraComplex))))))
        (fun (j : Nat) =>
          @HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul) (s j)
            (@HPow.hPow.{0, 0, 0} Complex Nat Complex
              (@instHPow.{0, 0} Complex Nat
                (@NPow.toPow.{0} Complex
                  (@Monoid.toNPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
              (@Inv.inv.{0} Complex Complex.instInv
                (@HPow.hPow.{0, 0, 0} Complex Nat Complex
                  (@instHPow.{0, 0} Complex Nat
                    (@NPow.toPow.{0} Complex
                      (@Monoid.toNPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
                  (@Int.cast.{0} Complex Complex.instIntCast x)
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
              j))
        μ (SummationFilter.unconditional.{0} Nat))
    (_hgap :
      @LT.lt.{0} Real Real.instLT
        (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
          (@OfNat.ofNat.{0} Real (nat_lit 128)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 128) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 127) (instOfNatNat (nat_lit 127)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 126) (instOfNatNat (nat_lit 126)))))))
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@OfNat.ofNat.{0} Real (nat_lit 6)
              (@instOfNatAtLeastTwo.{0} Real (nat_lit 6) Real.instNatCast
                (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 5) (instOfNatNat (nat_lit 5)))
                  (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))))
            r))
        (@HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
          (@HPow.hPow.{0, 0, 0} Real Nat Real
            (@instHPow.{0, 0} Real Nat (@NPow.toPow.{0} Real (@Monoid.toNPow.{0} Real Real.instMonoid)))
            (@Int.cast.{0} Real Real.instIntCast x) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@OfNat.ofNat.{0} Real (nat_lit 4)
            (@instOfNatAtLeastTwo.{0} Real (nat_lit 4) Real.instNatCast
              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
                (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
    (M : Int),
    @Ne.{1} Complex
      (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
        (@HPow.hPow.{0, 0, 0} Complex Nat Complex
          (@instHPow.{0, 0} Complex Nat
            (@NPow.toPow.{0} Complex
              (@Monoid.toNPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))))
          (@Int.cast.{0} Complex Complex.instIntCast x) r)
        μ)
      (@Int.cast.{0} Complex Complex.instIntCast M))
  Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration)

noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.roleEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (PUnit.{1}) where
  values := [PUnit.unit.{1}]
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.anchorEnumeration : LeanInformationAudit.Contract.FiniteEnumeration (Empty) where
  values := []
  nodup := by decide +kernel
  complete := by decide +kernel

noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.observation0 : (s : Nat → Complex) →
  (r : Nat) →
    (hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r) →
      (x : Int) →
        (hx : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) x) →
          (μ : Complex) →
            (hs0 :
                @Eq.{1} Complex (s (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
                  (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
              (j : Nat) →
                @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j →
                  (z : Int) →
                    D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Signature.Output.{0, 0, 0, 0, 0}
                      Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.signature PUnit.unit.{1} s :=
  fun (s : Nat → Complex) (r : Nat)
    (hr : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) r) (x : Int)
    (hx : @LT.lt.{0} Int Int.instLTInt (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) x) (μ : Complex)
    (hs0 :
      @Eq.{1} Complex (s (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
        (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne)))
    (j : Nat) (a : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) j)
    (z : Int) =>
  @D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Realization.readout.{0, 0, 0, 0, 0}
    Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.signature
    Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.actual PUnit.unit.{1} s j

noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.observationFact0 : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"dyadic_series_integer_obstruction\"],\"part\":\"type\",\"path\":[\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"body\",\"domain\",\"body\",\"body\",\"argument\",\"body\",\"argument\",\"function\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"registration_1\",\"observation0\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.dyadic_series_integer_obstruction, part := .type, path := [.body, .body, .body, .body, .body, .body, .body, .domain, .body, .body, .argument, .body, .argument, .function, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.observation0, part := .value, path := [], levels := [] }
  (by first | rfl | (ext <;> rfl))

noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.varyingLawInput :=
  D5.S3.ConceptDynamics.InformationEscape.DependentFamily.Arena.Law (Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.canonicalArenaOperand)
noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.varyingLaw  :=
  compiled_head% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"registration_1\",\"varyingLawInput\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"

noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.statementExclusion : LeanInformationAudit.Contract.StatementExclusion (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"registration_1\",\"varyingLaw\"],\"part\":\"value\",\"path\":[],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"dyadic_series_integer_obstruction\"],\"part\":\"type\",\"path\":[],\"levels\":[]}")) where
  lawLocation := { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.varyingLaw, part := .value, path := [], levels := [] }
  statementLocation := { owner := `D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.dyadic_series_integer_obstruction, part := .type, path := [], levels := [] }
  excludes := Reg.Support.NodeFacts.excludeFixed _ _ (Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration).actual (Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration).variation.2.choose (Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration).variation.1 (Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration).variation.2.choose_spec

noncomputable def Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1.descriptorFact : LeanInformationAudit.Contract.NodeFact := .equal
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S3\",\"Arith\",\"Primes\",\"DyadicSeriesIntegerObstruction\",\"registration\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"argument\"],\"levels\":[]}"))
  { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction, declaration := `Reg.D5.S3.Arith.Primes.DyadicSeriesIntegerObstruction.registration, part := .value, path := [.function, .function, .function, .function, .argument], levels := [] }
  (by first | rfl | (ext <;> rfl))
