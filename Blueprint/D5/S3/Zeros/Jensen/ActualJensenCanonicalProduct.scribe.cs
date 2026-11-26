using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class ActualJensenCanonicalProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/Jensen/ActualJensenCanonicalProduct.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The multiplicity-indexed xi-square product constructs the actual theta Jensen tower under the critical-line condition.",
        H("The actual Jensen criterion from the canonical product"),
        Blocks(
            Describe.Lean(DescribeId.Create("first-order-real-root-preservation"),
                DeclarationHandle.Create(Prefix + "firstOrder_preserves_real"),
                H("Real first-order differential operators preserve root reality"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let p be a complex polynomial with only real roots and let a be any real scalar. Then p minus a times its formal derivative has only real roots. At a nonreal point the logarithmic derivative sums the reciprocals of the differences from all roots, counting multiplicity. When the root multiset is nonempty, its imaginary part is minus the imaginary part of the point times a strictly positive sum. The empty multiset gives a constant polynomial, and the zero scalar gives the original polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-jensen-tower-from-zero-line"),
                DeclarationHandle.Create(Prefix + "actual_jensen_tower_of_zero_line"),
                H("Construction at every positive degree"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume every nontrivial zeta zero has real part one half. Then for every natural degree d at least one, the actual fixed zero-shift sourceJensenPolynomial(d) has only real roots.")),
                    Paragraph(Text("Under the line condition the square reciprocals of the canonical spectral parameters are real. For each finite set of multiplicity indices let P be the product of the corresponding linear factors. Substitute the formal derivative for the indeterminate and apply P to the monomial Y to the power d. Each factor acts by a real first-order differential operator, so this Appell polynomial has only real roots.")),
                    Paragraph(Text("For a nonzero complex z, evaluation of the normalized Jensen polynomial of P equals the Appell polynomial evaluated at d divided by z and multiplied by (z divided by d) to the power d. This follows by comparing the finite coefficients with falling factorial weights. Local uniform convergence of the canonical product implies convergence of each Taylor coefficient. The finite Jensen sum at this fixed d therefore converges locally uniformly to the reflected source polynomial. Its constant term is one, so Cauchy zero exclusion and reflection give root reality for the source polynomial."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-iff-actual-jensen-tower"),
                DeclarationHandle.Create(Prefix + "rh_iff_actual_jensen_tower"),
                H("Equivalence with the full actual Jensen tower"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Riemann hypothesis holds if and only if sourceJensenPolynomial(d) has only real roots for every natural d at least one. These are the literal theta-moment polynomials at zero shift, with the falling-factorial weight divided by the degree to the corresponding power. The forward implication uses the canonical product and the reverse implication uses local uniform approximation of the xi-square source."))),
                DescribeRole.Theorem))));
}
