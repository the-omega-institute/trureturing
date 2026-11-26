using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class ThirdTwistedChargeActionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/ThirdTwistedChargeAction.";
    private static readonly LibraryNoteRef TwistedCharges =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descent of the normalized moving-charge scalar and construction of the order-three charge operators on the integral momentum module.",
        H("Order-Three Momentum Charge Action"),
        Blocks(
            Paragraph(Text("Use the native symmetric even integral lattice, an additive equivalence g with g³ = 1, "
                + "and preservation of the pairing ⟨·,·⟩. Write d = 1 − g and N = 1 + g + g². "
                + "The input Multiplier consists of a normalized bimultiplicative complex-unit multiplier c, "
                + "a unit ζ with ζ³ = 1, and the relation c(d a,b)/c(b,d a) = ζ to the power −⟨N a,b⟩. "
                + "The input LiftPhase consists of η with η(a)η(b)c(a,b) = η(a+b)c(g a,g b) and η = 1 on fixed charges. "
                + "The concrete multiplier and moving commutator come from ThirdTwistedChargeCocycle, based on "
                + "Bakalov–Kac, arXiv:math/0402315v3, §4.3, equations (4.42) and (4.43).")),
            Describe.Lean(
                DescribeId.Create("third-charge-action-norm-difference"),
                DeclarationHandle.Create(Prefix + "norm_difference"),
                H("The difference lies in the norm kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For g³ = 1, the integral telescoping sum N(d a) = 0 uses only additivity of g. "
                    + "Thus every difference charge is a member of the moving lattice ker N."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-shift"),
                DeclarationHandle.Create(Prefix + "bShift"),
                H("Rational charge shift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(TwistedCharges),
                Blocks(Paragraph(Text("Equation (4.27) of BK uses half the difference of the squared norms of the "
                    + "fixed projection and the original charge. The integral formula is bShift(a) = (⟨N a,N a⟩/9 − ⟨a,a⟩)/2."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-charge-action-shift-integrality"),
                DeclarationHandle.Create(Prefix + "three_mul_bShift"),
                H("The shift has an integral numerator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("For the period-three isometry, N is self-adjoint for the pairing and its image is fixed. "
                    + "Consequently 3 bShift(a) = q(a), where q(a) = ⟨a,g a⟩ − ⟨a,a⟩."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-polarization"),
                DeclarationHandle.Create(Prefix + "q_polarization"),
                H("Polarization of the integral numerator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Expanding both pairings and using preservation of the form and g³ = 1 gives "
                    + "q(a+b) − q(a) − q(b) = ⟨N a,b⟩ − 3⟨a,b⟩."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-native-phase"),
                DeclarationHandle.Create(Prefix + "nativeStandardEta"),
                H("Native standard phase"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("If τ is IsometryLift.phase, define η(a) = τ(a)/τ(N a). The normalization implements "
                    + "the fixed-charge convention of BK (4.18)–(4.19) using the native lattice lift."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-charge-action-native-fixed"),
                DeclarationHandle.Create(Prefix + "nativeStandardEta_fixed"),
                H("Normalization on fixed charges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("For an isometry, the native sign phase is multiplicative on fixed charges and has square one. "
                    + "When g a = a, its norm phase is τ(3a) = τ(a), so the corrected phase is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-native-lift"),
                DeclarationHandle.Create(Prefix + "nativeLiftPhase"),
                H("Transfer to the twisted multiplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("Assume in addition c(a,b)ε(a,b) = c(g a,g b)ε(g a,g b) in the complex numbers, "
                    + "where ε is the native lattice sign. The native phase law gives the multiplier phase law by cancellation. "
                    + "The inverse norm phase is a character since N a and N b are fixed, so the correction preserves the law. "
                    + "This constructs the LiftPhase with the stated normalization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-charge-action-moving-scalar"),
                DeclarationHandle.Create(Prefix + "f"),
                H("Difference-charge scalar at zero momentum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("The scalar f(a) = η(a)⁻¹ c(g a,d a) ζ to the power −q(a) is the form of "
                    + "BK (4.46) obtained from the charge d a of the ordered product U_(g a)⁻¹ U_a "
                    + "and the multiplier relation (4.42)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-charge-action-scalar-multiplication"),
                DeclarationHandle.Create(Prefix + "f_mul"),
                H("Twisted multiplication before descent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("The lift-phase law and bimultiplicativity expand f(a)f(b)/(c(d a,d b)f(a+b)) "
                    + "into the moving commutator against g b and the phase of the polarization of q. "
                    + "The exponents cancel to −3⟨a,b⟩, whose phase is one by ζ³ = 1. "
                    + "Thus f(a)f(b) = c(d a,d b) f(a+b)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-scalar-descent"),
                DeclarationHandle.Create(Prefix + "f_congr"),
                H("Descent along the difference map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("If d a = d b then a − b is fixed. The normalized scalar of a fixed charge is one, "
                    + "and the twisted multiplication with this fixed difference reduces to f(a) = f(b)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-momentum-descent"),
                DeclarationHandle.Create(Prefix + "fAt_congr"),
                H("Descent of the nonzero-momentum scalar"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("The momentum scalar fAt(a,b) is f(a) times ζ to the power −⟨N a,b⟩. "
                    + "The moving commutator and self-adjointness of N prove that it depends only on d a and N b. "
                    + "With physical momentum N b / 3 this is the fixed-momentum phase in BK (4.46)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-integral-exactness"),
                DeclarationHandle.Create(Prefix + "MovingExact"),
                H("Integral moving-lattice exactness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("MovingExact requires every integral charge in ker N to lie in range d. "
                    + "When g³ = 1, norm_difference gives the reverse inclusion, so this is ker N = range d. "
                    + "This hypothesis extends the descended scalar to every moving charge. "
                    + "The P48q application supplies it from the Nebe row-lattice moving certificate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-charge-action-chi"),
                DeclarationHandle.Create(Prefix + "chi"),
                H("Scalar on the moving lattice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("With MovingExact, choose a preimage a of each m in ker N under d and set χ(m) = f(a). "
                    + "The theorem chi_difference follows from f_congr and identifies the value on every difference representative."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-charge-action-chi-mul"),
                DeclarationHandle.Create(Prefix + "chi_mul"),
                H("Multiplication on the integral moving subgroup"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("Choose integral difference representatives a and b for m and n in ker N. "
                    + "The difference of a+b represents m+n. Descending f_mul proves χ(m)χ(n) = c(m,n)χ(m+n)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-coefficient"),
                DeclarationHandle.Create(Prefix + "coefficient"),
                H("Coefficient for a momentum translation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("Index the projected momenta by p ∈ range N, representing p/3. Choose a section s "
                    + "with N(s(p)) = p. The shift by a is p′ = p + N a, and the difference "
                    + "m = a + s(p) − s(p′) lies in ker N. Define the coefficient as c(a,s(p)) χ(m)/c(s(p′),m)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-charge-action-coefficient-mul"),
                DeclarationHandle.Create(Prefix + "coefficient_mul"),
                H("Multiplication of the translation coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("Successive shifts by b and a equal the shift by a+b. The section differences add, "
                    + "and the identity c(a,b)c(a+b,t) = c(b,t)c(a,b+t) follows from bimultiplicativity. "
                    + "Together with chi_mul this gives coefficient(b,p) coefficient(a,p+N b) = c(a,b) coefficient(a+b,p)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-linear-operator"),
                DeclarationHandle.Create(Prefix + "U"),
                H("Actual charge operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("Ground is the complex Finsupp module on range N. Extend the action on each "
                    + "momentum basis vector linearly using Finsupp.lsum. The operator U(a) shifts p to p+N a "
                    + "and multiplies its coefficient by coefficient(a,p)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("third-charge-action-unit"),
                DeclarationHandle.Create(Prefix + "U_zero"),
                H("Unit operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("The shift and section difference at a = 0 are p and zero respectively. "
                    + "The normalized multiplier and χ(0) = 1 give U(0) equal to the identity on Ground."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-composition"),
                DeclarationHandle.Create(Prefix + "U_comp"),
                H("Twisted group algebra multiplication"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("The coefficient multiplication holds at every momentum, and finite-support linear-map "
                    + "extensionality gives U(a) composed with U(b) = c(a,b) U(a+b) on the whole Ground module. "
                    + "This realizes BK (4.42) for the charge operators with the stated algebraic inputs and integral exactness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("third-charge-action-moving-relation"),
                DeclarationHandle.Create(Prefix + "U_difference_single"),
                H("Moving-charge relation at every momentum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(TwistedCharges),
                Blocks(Paragraph(Text("The shift by d a fixes p and its section difference is d a. The commutator ratio "
                    + "c(d a,s(p))/c(s(p),d a) equals ζ to the power −⟨N a,s(p)⟩, and χ(d a) = f(a). "
                    + "Thus U(d a) on the momentum vector with complex coefficient z is multiplication by fAt(a,s(p)). "
                    + "This proves the moving scalar from BK (4.46) on actual momentum states."))),
                DescribeRole.Theorem),
            Paragraph(Text("The scope is the charge action conditional on the normalized multiplier, compatible lift phase and "
                + "integral exactness. The concrete P48q inputs, oscillator field construction and full orbifold obstruction "
                + "are subsequent mathematical steps.")))));
}
