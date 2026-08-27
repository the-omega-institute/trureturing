using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Connectivity;

internal sealed class GoldenDisplacementSeriesValueConnectednessDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Analytic/Connectivity/GoldenDisplacementSeriesValueConnectedness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The attained golden displacement values form a path-connected set with no gaps above one.",
        H("Path-Connectedness of Golden Displacement Series Values"),
        Blocks(
            Paragraph(Text(
                "The exact convergence region is convex, and the golden displacement sum is "
                + "continuous on that region. The unattained greatest lower bound at one "
                + "supplies an attained value and hence a point in the convergence region. "
                + "The region and its continuous image are therefore path-connected.")),
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-values-path-connected"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                    + "golden_displacement_series_values_isPathConnected"),
                H("The attained value set is path-connected"),
                StatementSource.FromAuthor(PathConnectedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The greatest-lower-bound and nonattainment declarations produce an "
                        + "attained value strictly between one and two. Its parameters give a "
                        + "point in the exact convergence region.")),
                    Paragraph(Text(
                        "That region is convex and nonempty, hence path-connected. Continuity of "
                        + "the series sum on this exact domain makes its image path-connected, "
                        + "and the image is exactly the displayed two-parameter value set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-no-gaps"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                    + "Ioo_one_subset_golden_displacement_series_values"),
                H("Every intermediate value above one is attained"),
                StatementSource.FromAuthor(NoGapsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Given an attained value x and a real y strictly between one and x, the "
                        + "greatest-lower-bound theorem and nonattainment of one provide an "
                        + "attained value z strictly between one and y. Order-connectedness of "
                        + "the path-connected value set then places y between the attained "
                        + "endpoints z and x, so y is attained.")),
                    Paragraph(Text(
                        "These theorems do not identify the value set with the open ray above "
                        + "one, assert that every real greater than one is attained, prove that "
                        + "the value set is unbounded above, or claim divergence to infinity at "
                        + "the boundary of the convergence region."))),
                DescribeRole.Theorem))));

    private static Formula PathConnectedFormula() =>
        F.Disp(Call("IsPathConnected", FullValueSet()));

    private static Formula NoGapsFormula()
    {
        Formula x = F.Id("x");
        return F.Disp(F.Seq(
            F.Forall, F.Sp, x, F.Sp, F.InMacro, F.Sp, FullValueSet(), F.Comma, F.RowBreak,
            Call("Ioo", F.D(1), x), F.Sp, F.Subseteq, F.Sp, FullValueSet(), F.Dot));
    }

    private static Formula FullValueSet()
    {
        Formula x = F.Id("x");
        Formula s = F.Id("s");
        Formula w = F.Id("w");
        return F.Seq(
            F.Left, F.OpenBrace, x, F.Sp, F.Colon, F.Sp, Reals(),
            F.Sp, F.Mid, F.Sp,
            F.Exists, F.Sp, s, F.Comma, F.Sp, w,
            F.Sp, F.InMacro, F.Sp, Reals(), F.Comma, F.Sp,
            Call("Summable", Call("dTerm", s, w)),
            F.Sp, F.Land, F.RowBreak,
            Tsum(s, w), F.Sp, F.Eq, F.Sp, x,
            F.Right, F.CloseBrace);
    }

    private static Formula Reals() => F.Seq(F.Mathbb, F.Grp(F.Id("R")));

    private static Formula Tsum(Formula s, Formula w)
    {
        Formula n = F.Id("n");
        return F.Seq(
            F.Sum, F.Underscore, F.Grp(n, F.Eq, F.D(0)),
            F.Caret, F.Grp(F.Infty), F.Sp, Call("dTerm", s, w, n));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq(pieces.ToArray());
    }
}
