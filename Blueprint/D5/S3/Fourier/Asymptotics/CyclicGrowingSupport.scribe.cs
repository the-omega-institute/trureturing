using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CyclicGrowingSupportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/CyclicGrowingSupport";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact positive support and optimizer certification in the critical growing-window regime.",
        H("Strict rear activation thresholds"),
        Blocks(
            Paragraph(Text(
                "Let the positive integer periods q(n) have eventual parity e in {0,1}, " +
                "write h(n)=2π/q(n), and assume n⁵h(n)² tends to a finite K. " +
                "The front window is the image in the cyclic group of integers −n through n. " +
                "The rear window of index l comprises offsets −l−e/2 through l+e/2 in unit steps " +
                "from the antipodal angle. Fit the three scaled moment equations on these windows.")),
            Describe.Lean(DescribeId.Create("strict-growing-support"),
                DeclarationHandle.Create(Owner + ".eventual_strict_support_away_from_thresholds"),
                H("Eventual exact support away from rear activation thresholds"),
                StatementSource.FromAuthor(Threshold()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Define T₀(l)=l(2l−1)(2l+1)/4 and T₁(l)=l(l+1/2)(l+1). " +
                        "Assume 3K/20 differs from every Tₑ(l). Then K is positive and monotonicity " +
                        "and unboundedness of the threshold polynomial give a unique index l " +
                        "between consecutive thresholds.")),
                    Paragraph(Text(
                        "The fitted values on the front and rear windows converge with the " +
                        "boundary scalings n² and n³. The endpoint and next-site signs at the front " +
                        "are strict. At the rear, the finite parity square sum identifies the " +
                        "strict inequalities of the limiting parabola with the two threshold inequalities. " +
                        "The signed cyclic values are a quadratic in the sampled cosine. Convexity " +
                        "and the four boundary signs determine its sign on the full grid.")),
                    Paragraph(Text(
                        "For all sufficiently large n the disjoint grid windows realize exactly the " +
                        "coupled moment sums. The fitted weights, extended by zero outside them, " +
                        "are feasible, attain both cosine moment floors 1−2n(n+1)h²/5, and uniquely " +
                        "minimize energy. Every feasible competitor w has energy at least the fitted " +
                        "energy plus the squared distance from w to the fit. The optimizer has " +
                        "strictly positive support precisely on the two windows. Equality at a rear " +
                        "threshold is excluded."))),
                DescribeRole.Theorem))));

    private static Formula Threshold()
    {
        var t = F.Id("T");
        var l = F.Id("l");
        var e = F.Id("e");
        var k = F.Id("K");
        var q = new Formula.Fraction(new Formula.Binary(F.D(3), FormulaBinaryOperator.Multiply, k),
            F.Seq(F.D(2), F.D(0)));
        var left = Call("Threshold", t, e, l);
        var right = Call("Threshold", t, e, new Formula.Binary(l, FormulaBinaryOperator.Add, F.D(1)));
        return F.Disp(new Formula.RelationChain(FormulaRelationOperator.LessThan, [left, q, right]));
    }
}
