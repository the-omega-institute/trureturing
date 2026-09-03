using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class ObserverSignedSupportBarcodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Observer-dependent negative support is exactly the open reflected-orbit barcode.",
        H("Observer Signed-Support Barcode"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("observer-signed-support"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerSignedSupport"),
                H("Observer-dependent signed support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The support coordinate is the squared height mismatch minus the squared transverse displacement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("orbit-active-at"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/ObserverSignedSupportBarcode.orbitActiveAt"),
                H("Active orbit interval"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An orbit is active when the observation parameter lies strictly inside its reflected interval."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("observer-localized-weight"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observerLocalizedWeight"),
                H("Localized signed weight"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Positive atomic mass multiplies the observer-dependent signed support."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("active-orbit-count"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/ObserverSignedSupportBarcode.activeOrbitCount"),
                H("Active barcode count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite count records all active reflected-orbit intervals."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("negative-localized-weight-count"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negativeLocalizedWeightCount"),
                H("Negative localized-weight count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite count records all strictly negative mass-times-support weights."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("observer-signed-support-neg-iff-active"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/ObserverSignedSupportBarcode.observer_signed_support_neg_iff_active"),
                H("Negative support is equivalent to interval activity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quadratic inequality is exactly the absolute-value interval condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-count-eq-active-count"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/ObserverSignedSupportBarcode.negative_localized_weight_count_eq_active_orbit_count"),
                H("Positive masses preserve the barcode count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Strictly positive masses preserve every support sign, so the two finite filters are equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("exists-active-iff-negative-weight"),
                DeclarationHandle.Create("D5/S3/Weil/Pick/ObserverSignedSupportBarcode.exists_active_orbit_iff_exists_negative_localized_weight"),
                H("Active orbit existence equals negative-weight existence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The pointwise sign equivalence is lifted to finite existential detection."))),
                DescribeRole.Theorem)
        ),
        []));
}
