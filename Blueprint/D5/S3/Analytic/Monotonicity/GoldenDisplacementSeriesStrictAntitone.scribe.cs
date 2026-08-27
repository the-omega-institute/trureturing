using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Monotonicity;

internal sealed class GoldenDisplacementSeriesStrictAntitoneDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A strict coordinate increase strictly lowers the golden displacement sum.",
        H("Strict Antitonicity of the Golden Displacement Series"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-displacement-series-strict-antitone"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Monotonicity/GoldenDisplacementSeriesStrictAntitone."
                    + "golden_displacement_series_strict_antitone"),
                H("A strict coordinate increase strictly lowers the sum"),
                StatementSource.FromAuthor(StrictAntitoneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take a parameter pair (s1,w1) where dTerm is summable. If both "
                        + "coordinates weakly increase and at least one strictly increases, "
                        + "then the sum at (s2,w2) is strictly smaller than the sum at "
                        + "(s1,w1).")),
                    Paragraph(Text(
                        "The module exports the termwise parameter-order inequality as "
                        + "dTerm_le_of_parameters_le. At index two, the public identity "
                        + "goldenSubstStart(1)=2 gives nS(2)=4, so both real-power bases "
                        + "are strictly greater than one.")),
                    Paragraph(Text(
                        "The base-greater-than-one real-power theorem makes the factor for "
                        + "the strictly increased coordinate strictly smaller. The other "
                        + "factor is weakly smaller and all factors are positive. Mathlib's "
                        + "Summable.tsum_lt_tsum_of_nonneg then promotes the strict inequality "
                        + "at index two and the termwise inequalities to a strict sum bound.")),
                    Paragraph(Text(
                        "The implication form follows the earlier frozen non-strict companion "
                        + "and avoids "
                        + "a StrictAntiOn domain interface with redundant membership data. "
                        + "Only summability at the original parameter pair is assumed; the "
                        + "strict comparison theorem derives summability of the smaller "
                        + "term family internally.")),
                    Paragraph(Text(
                        "The public termwise lemma is the usable authoritative declaration "
                        + "for new consumers. The earlier frozen non-strict companion keeps "
                        + "its own private "
                        + "copy: revoking a valid frozen node is an errata remedy, not an "
                        + "API-refactoring mechanism.")),
                    Paragraph(Text(
                        "The theorem does not claim a quantitative gap, an equality "
                        + "characterization, a converse, strict decrease when both parameters "
                        + "are unchanged, or a finite sum value."))),
                DescribeRole.Theorem))));

    private static Formula StrictAntitoneFormula()
    {
        Formula s1 = Indexed("s", 1);
        Formula w1 = Indexed("w", 1);
        Formula s2 = Indexed("s", 2);
        Formula w2 = Indexed("w", 2);
        Formula variables = F.Seq(
            s1, F.Comma, F.Sp, w1, F.Comma, F.Sp,
            s2, F.Comma, F.Sp, w2);
        Formula assumptions = F.Seq(
            Call("Summable", Call("dTerm", s1, w1)),
            F.Sp, F.Land, F.Sp, s1, F.Sp, F.Leq, F.Sp, s2,
            F.Sp, F.Land, F.Sp, w1, F.Sp, F.Leq, F.Sp, w2,
            F.Sp, F.Land, F.Sp, F.Open,
            s1, F.Sp, F.Lt, F.Sp, s2,
            F.Sp, F.Lor, F.Sp,
            w1, F.Sp, F.Lt, F.Sp, w2, F.Close);

        return F.Disp(F.Seq(
            F.Forall, F.Sp, variables, F.Sp, F.InMacro, F.Sp,
            F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Quad,
            assumptions, F.Sp, F.Rightarrow, F.RowBreak,
            Tsum(s2, w2), F.Sp, F.Lt, F.Sp, Tsum(s1, w1), F.Dot));
    }

    private static Formula Tsum(Formula s, Formula w)
    {
        Formula n = F.Id("n");
        return F.Seq(
            F.Sum, F.Underscore, F.Grp(n, F.Eq, F.D(0)),
            F.Caret, F.Grp(F.Infty), F.Sp, Call("dTerm", s, w, n));
    }

    private static Formula Indexed(string name, byte index) =>
        F.Seq(F.Id(name), F.Underscore, F.D(index));

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
