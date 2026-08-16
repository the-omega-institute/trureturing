using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure;

internal sealed class PositiveSeriesTailDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive tail term makes the total exceed its finite partial sum.",
        H("Positive Series Tails"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-partial-sum-strictly-below-positive-series"),
                DeclarationHandle.Create(
                    "D5/S3/AnalyticClosure/PositiveSeriesTail."
                    + "finite_partial_sum_lt_tsum_of_pos_outside"),
                H("A positive tail forces a strict partial-sum bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open,
                    Open, Forall, Sp, F.Id("n"), Comma, Sp,
                    D(0), Sp, Leq, Sp, F.Id("a"), Underscore, F.Id("n"), Close,
                    Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Summable")), Open, F.Id("a"), Close,
                    Sp, Land, Sp,
                    Open, Exists, Sp, F.Id("i"), Sp, InMacro, Sp,
                    F.Id("W"), Caret, F.Id("c"), Comma, Sp,
                    D(0), Sp, Lt, Sp, F.Id("a"), Underscore, F.Id("i"), Close,
                    Close, Sp, Rightarrow, Sp,
                    Sum, Underscore, Grp(F.Id("n"), Sp, InMacro, Sp, F.Id("W")), Sp,
                    F.Id("a"), Underscore, F.Id("n"), Sp, Lt, Sp,
                    Sum, Underscore, Grp(F.Id("n"), Eq, D(0)), Caret, Grp(Infty), Sp,
                    F.Id("a"), Underscore, F.Id("n")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a be a nonnegative summable real sequence and W a finite set of "
                        + "indices. If some strictly positive term lies outside W, then the sum "
                        + "over W is strictly smaller than the infinite sum of the sequence.")),
                    Paragraph(Text(
                        "The proof truncates the sequence to W and applies Mathlib's strict "
                        + "comparison theorem Summable.tsum_lt_tsum_of_nonneg at the omitted "
                        + "positive index. The infinite sum of the truncation is then rewritten "
                        + "as the finite sum over W.")),
                    Paragraph(Text(
                        "This closes only the positive-series strictness used to exclude a finite "
                        + "partial sum as the final value in remark 27.193. It makes no claim "
                        + "about the even-insertion formula, the reported numerical mean, or "
                        + "higher-order "
                        + "families in that atom."))),
                DescribeRole.Theorem))));
}
