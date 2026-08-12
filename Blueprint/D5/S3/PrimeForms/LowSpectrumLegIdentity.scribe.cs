using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class LowSpectrumLegIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The recorded low-spectrum leg satisfies its exact integral quadratic-form identity.",
        H("Low-Spectrum Leg Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("low-spectrum-leg-identity"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/LowSpectrumLegIdentity.low_spectrum_leg_identity"),
                H("The recorded leg satisfies the quadratic form"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(4), Cdot, D(4, 3, 5, 7), Sp, Eq, Sp,
                    D(3), Cdot, D(3, 3), Caret, D(2), Sp, Plus, Sp,
                    D(1, 1, 9), Caret, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The concrete discriminant value 4357, denominator 33, and integral leg 119 "
                        + "obey 4 times 4357 equals 3 times 33 squared plus 119 squared. This is the "
                        + "exact natural-number check underlying the recorded low-spectrum value.")),
                    Paragraph(Text(
                        "The statement records only this closed arithmetic identity. It makes no claim "
                        + "about the surrounding continued-fraction classification or spectral ordering."))),
                DescribeRole.Theorem))));
}
