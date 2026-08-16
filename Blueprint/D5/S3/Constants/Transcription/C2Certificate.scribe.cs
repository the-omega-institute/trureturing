using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Transcription;

internal sealed class C2CertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The registered second coefficient satisfies its transcription and error certificates.",
        H("Second-Coefficient Transcription Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("second-coefficient-transcription-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Transcription/C2Certificate.c2_transcription_certificate"),
                H("The second-coefficient transcription is certified"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("c"), Underscore, D(2), Eq,
                    Frac, Grp(Sqrt, Grp(D(5)), Minus, D(1)), Grp(D(2)),
                    F.Id("B"), Underscore, F.Id("h"), Plus,
                    Open, D(3), Minus, Frac, Grp(D(7), Sqrt, Grp(D(5))), Grp(D(2)), Close,
                    F.Id("T"), Underscore, D(0), Plus,
                    D(3), Sqrt, Grp(D(5)), F.Id("T"), Underscore, D(1), Plus,
                    Frac, Grp(D(2, 6, 9), Sqrt, Grp(D(5)), Minus, D(6, 2, 3)),
                    Grp(D(4, 8)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The exact equality unfolds the frozen catalog definition. Rational "
                            + "enclosures of the positive square root of five certify the stated "
                            + "input and output error bars.")),
                    Paragraph(Text(
                        "The same bounds show that replacing the registered zero-moment center by "
                            + "its corrected closed form shifts the coefficient by less than the "
                            + "declared error. They also exclude the four recorded candidate values; "
                            + "the logarithmic exclusion uses the standard strict logarithm bound "
                            + "and the lower bound three for pi."))),
                DescribeRole.Theorem))));
}
