using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class LatticeSquareMomentActivationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Asymptotics/LatticeSquareMomentActivation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A second-moment budget on the integer lattice determines the support of the unique squared-mass minimizer.",
        H("Exact support thresholds on the integer lattice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-lattice-support-interval"),
                DeclarationHandle.Create(Owner + ".exists_lattice_square_moment_minimizer_on_interval"),
                H("The budgets for one radius interval"),
                StatementSource.FromAuthor(Interval()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here n is a positive integer and m is real. Activation(m,n,t,Z,w) requires "
                        + "n² ≤ t ≤ (n+1)² and Z = Σ_{|j|≤n}(t−j²) > 0. The law w on the integers is "
                        + "max(0,t−j²)/Z. It is nonnegative with convergent sums giving mass one "
                        + "and second moment m. Each budget endpoint occurs exactly at the corresponding "
                        + "endpoint for t. At t=n² the support is [−(n−1),n−1] in the integers. "
                        + "For n²<t≤(n+1)² the support is [−n,n]. At m=0 the law is the point mass at zero.")),
                    Paragraph(Text(
                        "For every nonnegative competitor v with mass one and convergent second moment s, "
                        + "its squared mass minus that of w equals Σ_j(v(j)−w(j))² + 2(m−s)/Z "
                        + "plus the summable nonnegative correction 2 Σ_j max(0,j²−t)v(j)/Z. "
                        + "If s≤m and v differs from w, its squared mass is strictly greater than that of w.")),
                    Paragraph(Text(
                        "Finite sums of squares and fourth powers give the normalized second moment at both endpoints. "
                        + "The denominator stays positive and the moment varies continuously, so every intermediate budget "
                        + "is attained. To prove the comparison, expand the squared masses and split the cross term "
                        + "into the affine function (t−j²)/Z and its correction outside the support."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lattice-moment-minimizer-for-all-budgets"),
                DeclarationHandle.Create(Owner + ".exists_lattice_square_moment_minimizer"),
                H("Coverage of all nonnegative budgets"),
                StatementSource.FromAuthor(Global()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real m≥0 choose n as the floor of sqrt(5m+1). "
                    + "The floor gives a positive index whose lower threshold is at most m and whose upper "
                    + "threshold is strictly greater. Conversely a nonnegative law has nonnegative second moment. "
                    + "The half-open intervals are disjoint. At a shared endpoint the closed intervals select the same law, "
                    + "radius parameter and normalizer. The laws agree by strict comparison. Since t≥1, "
                    + "the values w(0)=t/Z and w(0)−w(1)=1/Z then identify Z and t."))),
                DescribeRole.Theorem))));

    private static Formula RadiusBudget(Formula n, Formula m, Formula upperRelation)
    {
        var lower = new Formula.Fraction(
            Subtract(new Formula.Power(n, F.D(2)), F.D(1)), F.D(5));
        var upper = new Formula.Fraction(Multiply(n, Add(n, F.D(2))), F.D(5));
        return F.Seq(lower, F.Sp, F.Le, F.Sp, m, F.Sp, upperRelation, F.Sp, upper);
    }

    private static Formula Interval()
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var t = F.Id("t");
        var z = F.Id("Z");
        var w = F.Id("w");
        var exists = F.Seq(F.Exists, F.Bang, F.Sp, F.Open, t, F.Comma, z, F.Comma, w, F.Close, F.Quad,
            Call("Activation", m, n, t, z, w));
        var equivalence = new Formula.Logic(RadiusBudget(n, m, F.Le), FormulaLogicOperator.Iff, exists);
        return F.Disp(F.Seq(F.Forall, F.Sp, n, F.Comma, m, F.Quad,
            F.D(0), F.Sp, F.Lt, F.Sp, n, F.Quad, F.Longrightarrow, F.Quad,
            F.Open, equivalence, F.Close));
    }

    private static Formula Global()
    {
        var m = F.Id("m");
        var n = F.Id("n");
        var t = F.Id("t");
        var z = F.Id("Z");
        var w = F.Id("w");
        var exists = F.Seq(F.Exists, F.Bang, F.Sp, F.Open, n, F.Comma, t, F.Comma, z, F.Comma, w,
            F.Close, F.Quad,
            F.D(0), F.Sp, F.Lt, F.Sp, n, F.Comma, F.Sp, RadiusBudget(n, m, F.Lt), F.Comma, F.Sp,
            Call("Activation", m, n, t, z, w));
        var nonnegative = F.Seq(F.D(0), F.Sp, F.Le, F.Sp, m);
        return F.Disp(F.Seq(F.Forall, F.Sp, m, F.Quad,
            new Formula.Logic(nonnegative, FormulaLogicOperator.Iff, exists)));
    }
}
