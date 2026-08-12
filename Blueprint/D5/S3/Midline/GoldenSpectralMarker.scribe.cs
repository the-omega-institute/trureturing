using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class GoldenSpectralMarkerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reciprocal first golden exponent gives the explicit golden spectral marker.",
        H("Golden Spectral Marker"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reciprocal-first-golden-exponent"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/GoldenSpectralMarker.golden_spectral_marker"),
                H("The reciprocal first golden exponent is the spectral marker"),
                StatementSource.FromAuthor(Disp(Seq(
                    Frac, Grp(D(1)), Grp(F.Id("beta"), Open, D(1), Close),
                    Sp, Eq, Sp,
                    Frac, Grp(D(1)), Grp(F.Id("phi"), Caret, D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The existing golden exponent power law proves beta(1) = phi^2. "
                        + "Taking reciprocals gives the displayed marker directly, so the "
                        + "Lean declaration is a thin wrapper around that repository theorem.")),
                    Paragraph(Text(
                        "This is a partial closure of the source spectral chain. It does not "
                        + "identify beta(1) with the minimum positive model-set value, prove "
                        + "that its reciprocal is the Euler product's absolute-convergence "
                        + "abscissa, or establish the concluding encoding-sensitivity and "
                        + "uniqueness claim. Those three subitems remain unresolved."))),
                DescribeRole.Theorem))));
}
