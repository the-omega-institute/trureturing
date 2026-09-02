using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class ObserverSignedSupportBarcodeCoverageDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/ObserverSignedSupportBarcode.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Center-time consequences of the observer-dependent signed-support barcode.",
        H("Observer Signed-Support Barcode: Center Consequences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-support-at-the-orbit-center"),
                DeclarationHandle.Create(Prefix + "observer_signed_support_at_center"),
                H("Signed support at the orbit center"),
                StatementSource.FromAuthor(
                    F.Disp(F.Id("centerSupportEqualsNegativeTransverseSquare"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At time gamma, the height displacement vanishes and only the negative "
                        + "transverse square remains."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-center-is-active-exactly-off-axis"),
                DeclarationHandle.Create(Prefix + "orbit_active_at_center_iff"),
                H("The center is active exactly off axis"),
                StatementSource.FromAuthor(
                    F.Disp(F.Id("centerActiveIffTransverseDisplacementNonzero"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The open barcode interval contains its center precisely when its radius "
                        + "is nonzero."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/Pick/ObserverSignedSupportBarcode")),
        ]));
}
