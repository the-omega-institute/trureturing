using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Transcription;

internal sealed class PhiSecondTranscriptionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact T0 substitution yields the closed second-order golden-radical value.",
        H("Exact Second-Order Transcription"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("phi-second-transcription-exact"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Transcription/PhiSecondTranscription."
                        + "phi_second_transcription_exact"),
                H("The second-order transcription has an exact closed form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, D(1), Minus, Sqrt, Grp(D(5)), Close,
                    F.Id("T"), Underscore, Grp(D(0)), Plus,
                    Frac,
                    Grp(D(1, 5), Sqrt, Grp(D(5)), Minus, D(3, 3)),
                    Grp(D(8)), Eq,
                    Frac,
                    Grp(D(5), Sqrt, Grp(D(5)), Minus, D(7)),
                    Grp(D(2, 4)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here T0 is the deposited exact Sturmian-Dirichlet value "
                            + "(27 - 13 sqrt(5)) / 24. Substitution reduces the statement to "
                            + "the standard identity sqrt(5)^2 = 5.")),
                    Paragraph(Text(
                        "This theorem covers only the source's exact second-order "
                            + "transcription clause; it makes no claim about the surrounding "
                            + "reconstruction program or numerical certificates."))),
                DescribeRole.Theorem))));
}
