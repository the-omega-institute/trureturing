import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Algebra.TraceKernelFunctionPolarization
import Reg.Support.DependentFamily
open scoped BigOperators Matrix
open MvPolynomial Finset
open _root_.D5.S3.Quantum.Algebra.TraceKernelFunctionPolarization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
namespace Reg.D5.S3.Quantum.Algebra.TraceKernelFunctionPolarization
abbrev signature : Signature where
 Params := Σ _m : ℕ, ℕ
 State p := MvPolynomial (Fin p.1 ⊕ Fin p.2) ℂ
 Role := Unit
 finiteRole := inferInstance
 nonemptyRole := inferInstance
 Output _ _ := ℂ
 Anchor := Empty
 finiteAnchor := inferInstance

def actual : Realization signature := realize signature
 (fun _ p Q => coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin p.1 ⊕ Fin p.2 => 1)) Q)
 (fun e => nomatch e)
def rejected : Realization signature := realize signature
 (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
 signature := signature
 Law r := ∀ (m n N : ℕ) (hN : 1 ≤ N)
    (f : {Z : Matrix (Fin N) (Fin N) ℂ // Matrix.trace Z = 0} → {W : Matrix (Fin N) (Fin N) ℂ // Matrix.trace W = 0} → ℂ)
    (hSU : ∀ (U : Matrix (Fin N) (Fin N) ℂ), U ∈ Matrix.specialUnitaryGroup (Fin N) ℂ →
      ∀ Z W : {Z : Matrix (Fin N) (Fin N) ℂ // Matrix.trace Z = 0},
      ∀ hZ : Matrix.trace (U * Z.val * Uᴴ) = 0,
      ∀ hW : Matrix.trace (U * W.val * Uᴴ) = 0, f ⟨U * Z.val * Uᴴ, hZ⟩ ⟨U * W.val * Uᴴ, hW⟩ = f Z W)
    (P : MvPolynomial (Bool × (Fin N × Fin N)) ℂ)
    (hP : ∀ Z W, eval (fun e : Bool × (Fin N × Fin N) => if e.1 then W.val e.2.1 e.2.2 else Z.val e.2.1 e.2.2) P = f Z W)
    (hdegree : ∀ (a b : ℂ) Z W, f ⟨a • Z.val, by simp [Matrix.trace_smul, Z.property]⟩ ⟨b • W.val, by simp [Matrix.trace_smul, W.property]⟩ =
        a ^ m * b ^ n * f Z W),
    ∃ F : MultilinearMap ℂ (fun _ : Fin m ⊕ Fin n => Matrix (Fin N) (Fin N) ℂ) ℂ,
      (∀ x, F x = ((m.factorial : ℂ) * (n.factorial : ℂ))⁻¹ * r.readout () ⟨m,n⟩
          (eval₂ C (fun v : Bool × (Fin N × Fin N) => if v.1 then ∑ j : Fin n, C (x (Sum.inr j) v.2.1 v.2.2) * X (Sum.inr j)
            else ∑ i : Fin m, C (x (Sum.inl i) v.2.1 v.2.2) * X (Sum.inl i))
              (MvPolynomial.eval₂Hom MvPolynomial.C (fun e : Bool × (Fin N × Fin N) => MvPolynomial.X e - if e.2.1 = e.2.2 then MvPolynomial.C ((N : ℂ)⁻¹) * ∑ k : Fin N, MvPolynomial.X (e.1, k, k) else 0) P))) ∧
      (∀ Z W, F (Sum.elim (fun _ => Z.val) (fun _ => W.val)) = f Z W) ∧
      (∀ T : Matrix (Fin N) (Fin N) ℂ →ₗ[ℂ] Matrix (Fin N) (Fin N) ℂ,
        (∀ Z W : Matrix (Fin N) (Fin N) ℂ, eval (fun e : Bool × (Fin N × Fin N) => if e.1 then (T W) e.2.1 e.2.2 else (T Z) e.2.1 e.2.2) (MvPolynomial.eval₂Hom MvPolynomial.C (fun e : Bool × (Fin N × Fin N) => MvPolynomial.X e - if e.2.1 = e.2.2 then MvPolynomial.C ((N : ℂ)⁻¹) * ∑ k : Fin N, MvPolynomial.X (e.1, k, k) else 0) P) =
          eval (fun e : Bool × (Fin N × Fin N) => if e.1 then W e.2.1 e.2.2 else Z e.2.1 e.2.2) (MvPolynomial.eval₂Hom MvPolynomial.C (fun e : Bool × (Fin N × Fin N) => MvPolynomial.X e - if e.2.1 = e.2.2 then MvPolynomial.C ((N : ℂ)⁻¹) * ∑ k : Fin N, MvPolynomial.X (e.1, k, k) else 0) P)) →
        ∀ x, F (fun j => T (x j)) = F x) ∧
      (∀ U : Matrix.unitaryGroup (Fin N) ℂ, ∀ x, F (fun j => (U : Matrix (Fin N) (Fin N) ℂ) * x j * (U : Matrix (Fin N) (Fin N) ℂ)ᴴ) = F x)

def rejected_law : ¬ arena.Law rejected := by
 intro h
 obtain ⟨F, hF, hd, _, _⟩ := h 0 0 1 (by omega) (fun _ _ => 1)
   (by intros; rfl) (C 1) (by intros; simp) (by intros; simp)
 let z : {Z : Matrix (Fin 1) (Fin 1) ℂ // Matrix.trace Z = 0} := ⟨0, by simp⟩
 have hz := hF (Sum.elim (fun _ => z.val) (fun _ => z.val))
 have hr := hd z z
 simp only [rejected, realize, mul_zero] at hz
 rw [hz] at hr
 norm_num at hr

def registration : Registration arena (type_of% @trace_kernel_function_polarization) where
 actual := actual
 bridge := Iff.rfl
 variation := ⟨trace_kernel_function_polarization, rejected, rejected_law⟩
 sensitivity := by
  constructor
  · intro i
    change Unit at i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    change Unit at j
    exact (hj (Subsingleton.elim j i)).elim
  · intro i
    exact nomatch i
 dependence := by
  change ObservationalDependence signature actual
  intro i
  refine ⟨⟨0,0⟩, 0, C 1, ?_⟩
  change coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin 0 ⊕ Fin 0 => 1)) (0 : MvPolynomial (Fin 0 ⊕ Fin 0) ℂ) ≠
    coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin 0 ⊕ Fin 0 => 1)) (C 1 : MvPolynomial (Fin 0 ⊕ Fin 0) ℂ)
  have hzero : Finsupp.equivFunOnFinite.symm (fun _ : Fin 0 ⊕ Fin 0 => (1 : ℕ)) = 0 := by
   ext j; exact isEmptyElim j
  simp [hzero]

noncomputable def registration_1 :
 Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
  (@_root_.D5.S3.Quantum.Algebra.TraceKernelFunctionPolarization.trace_kernel_function_polarization)
  (type_of% (realize signature
   (fun _ p Q => coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin p.1 ⊕ Fin p.2 => 1)) Q)
   (fun e => nomatch e))) Unit Unit := {
 unitName := `D5.S3.Quantum.Algebra.TraceKernelFunctionPolarization.trace_kernel_function_polarization.__information_unit,
 realizationName := `Reg.D5.S3.Quantum.Algebra.TraceKernelFunctionPolarization.registration,
 realizationSource := none, generated := false,
 arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
 catalog := Lean.Name.anonymous, localNames := false,
 realization := .source arena ⟨registration⟩,
 correspondence := { stage := .evidence, objectStage := .evidence },
 bundleNonempty := .absent,
 readout := some (realize signature
   (fun _ p Q => coeff (Finsupp.equivFunOnFinite.symm (fun _ : Fin p.1 ⊕ Fin p.2 => 1)) Q)
   (fun e => nomatch e)),
 variation := .absent, sensitivity := .absent, partialSensitivity := none,
 escapeFrom := none,
 sourceSelection := some {
  owner := `D5.S3.Quantum.Algebra.TraceKernelFunctionPolarization, definition := none,
  coordinates := #[0,1], readouts := #[{
   path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
     "arg", "body", "fn", "arg", "body", "arg", "arg"], stateBinder := 0, functionOperand := false,
   stateOperand := some #["arg"], booleanPredicate := false }] },
 continuation := .unknown, familyRecord := none, options := #[] }
#print axioms registration
#print axioms registration_1
end Reg.D5.S3.Quantum.Algebra.TraceKernelFunctionPolarization
