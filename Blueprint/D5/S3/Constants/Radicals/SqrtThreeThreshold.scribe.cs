using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Radicals;

internal sealed class SqrtThreeThresholdDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "Twice root three lies strictly above three.",
            H("Square Root of Three Threshold"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("twice-root-three-exceeds-three"),
                    DeclarationHandle.Create(
                        "D5/S3/Constants/Radicals/SqrtThreeThreshold.three_lt_two_mul_sqrt_three"),
                    H("Twice root three exceeds three"),
                    StatementSource.FromAuthor(Disp(Seq(
                        D(3), Sp, Lt, Sp, D(2), Cdot, Sqrt, Grp(D(3)), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The secondary threshold in the source is strict: two times the "
                            + "square root of three is greater than three. The proof applies "
                            + "the pinned library's square-root comparison theorem to the "
                            + "rational inequality (3/2)^2 < 3, then rescales by two."))),
                    DescribeRole.Theorem
                ))));
}
