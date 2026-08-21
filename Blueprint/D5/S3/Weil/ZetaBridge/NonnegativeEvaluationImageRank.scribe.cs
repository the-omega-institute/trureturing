using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class NonnegativeEvaluationImageRankDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonnegative two-coordinate cross form has image dimension at most one.",
        H("Rank Bound for a Nonnegative Evaluation Image"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonnegative-two-coordinate-evaluations-have-rank-at-most-one"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/NonnegativeEvaluationImageRank."
                        + "nonnegative_evaluation_image_finrank_le_one"),
                H("A nonnegative evaluation image has rank at most one"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("T"), Comma, Sp,
                    Forall, Sp, F.Id("E"), Colon, Sp,
                    F.Id("T"), Sp, To, Sp, F.Id("C"), Caret, Grp(D(2)), Comma, Sp,
                    Forall, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    D(0), Lt, Sp, F.Id("m"), Sp, Land, Sp,
                    Grp(Forall, Sp, F.Id("g"), InMacro, Sp, F.Id("T"), Comma, Sp,
                        D(0), Leq, Sp, Operatorname, Grp(F.Id("CrossValue")), Open,
                        F.Id("m"), Comma, Sp, F.Id("E"), Open, F.Id("g"), Close, Close),
                    Sp, Rightarrow, RowBreak,
                    Grp(Operatorname, Grp(F.Id("dim")), Underscore, F.Id("C"), Open,
                        Operatorname, Grp(F.Id("im")), Open, F.Id("E"), Close, Close,
                        Sp, Leq, Sp, D(1), Sp, Land, Sp, Neg,
                        Operatorname, Grp(F.Id("Surjective")), Open, F.Id("E"), Close), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let T be a complex vector space and E a complex-linear map into two "
                            + "complex coordinates. A positive natural multiplicity weights the "
                            + "canonical real cross value from the neighboring module.")),
                    Paragraph(Text(
                        "Assume that cross value is nonnegative for every test. If the image had "
                            + "dimension two, the imported negative-direction theorem would "
                            + "produce a test with strictly negative cross value, a contradiction. "
                            + "The same "
                            + "rank bound rules out surjectivity onto both mirror coordinates.")),
                    Paragraph(Text(
                        "The zero evaluation witnesses that the hypotheses are jointly "
                            + "satisfiable. The proof reuses the canonical cross value and does not "
                            + "redeclare an "
                            + "evaluation or Hermitian-form object."))),
                DescribeRole.Theorem))));
}
