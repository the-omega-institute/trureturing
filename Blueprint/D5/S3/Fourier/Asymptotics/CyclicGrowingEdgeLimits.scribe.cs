using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicGrowingEdgeLimitsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicGrowingEdgeLimits";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Critical-scale coefficients and signed boundary values for growing cyclic windows.",
        H("Boundary limits in the growing cyclic moment fit"),
        Blocks(
            Paragraph(Text(
                "Fix a nonempty finite set S of real rear offsets and let n tend to infinity. " +
                "Assume n⁵h(n)² tends to a finite real K. Put m=n(n+1)/5 and prescribe the " +
                "three scaled moments (1−mh²,m/n²,3n³mh²/4). The coefficient vector a(n) is the " +
                "inverse of the coupled moment matrix applied to this target.")),
            Describe.Lean(DescribeId.Create("critical-coefficient-limit"),
                DeclarationHandle.Create(Owner + ".coefficient_tendsto"),
                H("The three fitted coefficients converge"),
                StatementSource.FromAuthor(Coefficients()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The moment target converges to (1,1/5,3K/20). Inverting the limiting " +
                    "coupled matrix gives (3/4,−3/4,B), where " +
                    "B=(3K/20+(3/4)∑_{r∈S}r²)/|S|."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("refined-front-coefficients"),
                DeclarationHandle.Create(Owner + ".refined_coefficients"),
                H("Front coefficient errors are bounded at scale n cubed"),
                StatementSource.FromAuthor(Refinement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The exact lattice reference has radius parameter t=n(n+1)−1/2 and " +
                    "normalizer Z. Its first two coefficients are nt/Z and −n³/Z. " +
                    "Assume the critical-scale quantity n⁵h² is bounded. After multiplying by n³, the top two rows of the coupled matrix minus " +
                    "the lattice Gram rows with a zero third column remain bounded. " +
                    "The scaled target mass perturbation also remains bounded. " +
                    "Holding the rear coefficient fixed, inversion of the first two rows " +
                    "transfers the bound to the two coefficient errors, which are O(n⁻³)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("front-edge-limit"),
                DeclarationHandle.Create(Owner + ".scaled_boundary_value"),
                H("Signed value at the growing front boundary"),
                StatementSource.FromAuthor(Front()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Boundedness of n⁵h² suffices. At x=(n+δ)/n the finite signed weight is the dot product of the coefficient " +
                    "row with a(n). Multiplying by n² gives the limit (3/4)(1−2δ). " +
                    "This gives strictly positive and strictly negative limiting values at δ=0 " +
                    "and δ=1 respectively. The scaled site-feature remainders vanish, including " +
                    "at a fixed offset beyond the fitted window."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("front-midpoint-limit"),
                DeclarationHandle.Create(Owner + ".boundary_midpoint_value"),
                H("Signed value at the half-step beyond the front boundary"),
                StatementSource.FromAuthor(Midpoint()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At δ=1/2 the leading n² limit vanishes. The coefficient and feature " +
                    "estimates transfer the next-order lattice value, yielding n³ times " +
                    "the signed weight tending to −9/16. The conclusion requires bounded n⁵h²."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rear-edge-limit"),
                DeclarationHandle.Create(Owner + ".scaled_rear_value"),
                H("Signed value at a fixed rear offset"),
                StatementSource.FromAuthor(Rear()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At every fixed real rear offset r the signed value multiplied by n³ " +
                    "converges to B−3r²/4. Strict limiting inequalities settle the eventual sign. " +
                    "Zero limiting values require finer estimates. These readouts concern a signed " +
                    "moment fit on the stated windows. Certification of the full cyclic optimizer " +
                    "also requires the cyclic grid correspondence and complement signs."))),
                DescribeRole.Theorem))));

    private static Formula Coefficients()
    {
        var a = F.Id("a");
        var n = F.Id("n");
        var b = F.Id("B");
        return F.Disp(Eq(Call("Limit", Call("Apply", a, n)),
            Call("VectorThree", Fraction(3, 4), Subtract(F.D(0), Fraction(3, 4)), b)));
    }

    private static Formula Refinement()
    {
        var n = F.Id("n");
        return F.Disp(Call("BigO", Multiply(new Formula.Power(n, F.D(3)),
            Subtract(Call("FrontCoefficients", n), Call("LatticeCoefficients", n))), F.D(1)));
    }

    private static Formula Front()
    {
        var n = F.Id("n");
        var d = F.Id("delta");
        return F.Disp(Eq(Call("Limit", Multiply(new Formula.Power(n, F.D(2)), Call("FrontValue", n, d))),
            Multiply(Fraction(3, 4), Subtract(F.D(1), Multiply(F.D(2), d)))));
    }

    private static Formula Midpoint()
    {
        var n = F.Id("n");
        return F.Disp(Eq(Call("Limit", Multiply(new Formula.Power(n, F.D(3)),
            Call("FrontValue", n, Fraction(1, 2)))), Subtract(F.D(0),
            new Formula.Fraction(F.D(9), F.Seq(F.D(1), F.D(6))))));
    }

    private static Formula Rear()
    {
        var n = F.Id("n");
        var r = F.Id("r");
        return F.Disp(Eq(Call("Limit", Multiply(new Formula.Power(n, F.D(3)), Call("RearValue", n, r))),
            Subtract(F.Id("B"), Multiply(Fraction(3, 4), new Formula.Power(r, F.D(2))))));
    }

    private static Formula Fraction(byte numerator, byte denominator) =>
        new Formula.Fraction(F.D(numerator), F.D(denominator));

    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Multiply(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Subtract(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
}
