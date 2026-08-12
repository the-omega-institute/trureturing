using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class RecordEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Two real interval integrals give the exact uniform binary-entropy average.",
            H("Record Entropy Integrals"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("negative-u-log-u-integrates-to-one-quarter"),
                    DeclarationHandle.Create("D5/S3/Constants/RecordEntropy.neg_mul_log_integral"),
                    H("Negative u log u integrates to one quarter"),
                    StatementSource.FromAuthor(Disp(Seq(
                                            Int, Underscore, Grp(D(0)), Caret, Grp(D(1)), Sp,
                                            Minus, F.Id("u"), Sp, Log, Sp, F.Id("u"), Sp, F.Id("du"),
                                            Eq, Frac, Grp(D(1)), Grp(D(4)), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                                            Paragraph(Text(
                                                "A continuous primitive built from u log u handles the singular "
                                                + "logarithmic endpoint. Mathlib's endpoint fundamental theorem of "
                                                + "calculus then evaluates the real interval integral exactly."))),
                    DescribeRole.Theorem
                ),
                Describe.Lean(
                    DescribeId.Create("uniform-binary-entropy-integral-in-bits"),
                    DeclarationHandle.Create("D5/S3/Constants/RecordEntropy.haar_record_entropy_bits"),
                    H("The uniform binary-entropy integral in bits"),
                    StatementSource.FromAuthor(Disp(Seq(
                                            Int, Underscore, Grp(D(0)), Caret, Grp(D(1)), Sp,
                                            Frac,
                                            Grp(
                                                Minus, F.Id("u"), Sp, Log, Sp, F.Id("u"), Sp, Minus, Sp,
                                                Open, D(1), Minus, F.Id("u"), Close, Sp, Log, Sp,
                                                Open, D(1), Minus, F.Id("u"), Close),
                                            Grp(Log, Sp, D(2)), Sp, F.Id("du"), Eq,
                                            Frac, Grp(D(1)), Grp(D(2), Sp, Log, Sp, D(2)), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                                            Paragraph(Text(
                                                "The substitution u maps to 1 - u identifies the two entropy "
                                                + "summands. Their integrals therefore add to one half, and division "
                                                + "by the natural logarithm of two converts the result to bits."))),
                    DescribeRole.Theorem
                ),
                DocumentBlock.Describe.Remark(
                    DescribeId.Create("physical-pushforward-is-out-of-scope"),
                    H("The physical pushforward is out of scope"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S3/Constants/RecordEntropy.haar_record_entropy_bits")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(
                        Paragraph(Text(
                            "The checked declaration is only a real interval identity for a "
                            + "uniform parameter u. It does not construct Bloch-sphere Haar "
                            + "measure or prove that measurement probability pushes that measure "
                            + "forward to the uniform distribution on [0, 1]. That bridge remains "
                            + "an unresolved X_Assumptions question, including how a classical "
                            + "assumption would relate to the no-new-axiom objective. The phrase "
                            + "record entropy carries the intended physical reading in this prose; "
                            + "the Lean type makes no physical claim and adds no axiom.")))
                ))));
}
