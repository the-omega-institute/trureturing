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
            Describe.Lean(DescribeId.Create("point-sign-certificate"),
                DeclarationHandle.Create(Owner + ".eventual_window_support_of_point_signs"),
                H("Pointwise boundary signs certify the optimizer"),
                StatementSource.FromAuthor(PointSigns()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any fixed rear index l, at sufficiently large n the front signs, " +
                    "matrix invertibility and dual coefficient inequalities hold. If the last " +
                    "included rear score is positive and the first omitted rear score is " +
                    "nonpositive at that n, the two-window fit is the unique optimizer, has " +
                    "the stated positive support and satisfies the squared-distance energy bound. " +
                    "The two conditions are imposed pointwise, so the omitted score may vanish."))),
                DescribeRole.Theorem),
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

    private static Formula PointSigns()
    {
        var r = F.Id("R");
        var at = Call("SignedValue", r);
        var next = Call("SignedValue", new Formula.Binary(r, FormulaBinaryOperator.Add, F.D(1)));
        var positive = new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, at);
        var nonpositive = new Formula.Relation(next, FormulaRelationOperator.LessThanOrEqual, F.D(0));
        var conclusion = new Formula.Relation(Call("Support", F.Id("v")),
            FormulaRelationOperator.Equal, Call("TwoWindows", F.Id("n"), F.Id("l")));
        return F.Disp(new Formula.Logic(new Formula.Logic(positive, FormulaLogicOperator.And, nonpositive),
            FormulaLogicOperator.Implies, conclusion));
    }

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
