using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants;

internal sealed class DeltaMeanArtifactDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create(
            "The corrected exchange-loss mean has zero absolute value.",
            H("Delta Mean Artifact"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("absolute-delta-mean-is-zero"),
                    DeclarationHandle.Create("D5/S3/Constants/DeltaMeanArtifact.abs_delta_mean_zero"),
                    H("The absolute corrected exchange-loss mean is zero"),
                    StatementSource.FromAuthor(Disp(Seq(
                        new Formula.Absolute(F.Id("deltaMean")),
                        Eq,
                        D(0),
                        Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The artifact defines the corrected exchange-loss mean as zero. "
                            + "Its absolute value therefore vanishes by direct simplification."))),
                    DescribeRole.Theorem
                ))));
}
