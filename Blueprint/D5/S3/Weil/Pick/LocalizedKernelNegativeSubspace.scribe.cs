using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class LocalizedKernelNegativeSubspaceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/LocalizedKernelNegativeSubspace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Active observer intervals define a finite coordinate model whose diagonal localized "
            + "quadratic form is strictly negative away from zero. Its coordinate cardinality "
            + "is exactly the signed-support barcode count.",
        H("Localized-Kernel Negative Coordinate Subspace"),
        Blocks(
            DefinitionNode("active-orbit-subtype", "ActiveOrbit",
                "Active orbit subtype",
                "Orbit labels whose observer-dependent signed support is negative at the selected time."),
            DefinitionNode("active-coordinate-negative-index", "activeCoordinateNegativeIndex",
                "Active-coordinate negative index",
                "The finite cardinality of the active-orbit coordinate type."),
            DefinitionNode("active-orbit-filter-equivalence", "activeOrbitEquivFiltered",
                "Active-orbit filter equivalence",
                "The active subtype is equivalent to the filtered universal finset used by the barcode count."),
            DefinitionNode("active-coordinate-quadratic", "activeCoordinateQuadratic",
                "Active-coordinate quadratic form",
                "The diagonal sum of localized atomic weights times coordinate squares."),
            DefinitionNode("exact-active-coordinate-transport", "ExactActiveCoordinateTransport",
                "Exact active-coordinate transport",
                "An injective linear realization together with an exact target quadratic readout."),
            TheoremNode("coordinate-index-equals-barcode-count",
                "active_coordinate_negative_index_eq_active_orbit_count",
                "The coordinate index equals the barcode count",
                "activeCoordinateIndexEqualsBarcodeCount",
                "Finite-cardinality transport through the filter equivalence identifies the two counts exactly."),
            TheoremNode("every-active-coordinate-weight-is-negative",
                "active_coordinate_weight_neg",
                "Every active coordinate weight is negative",
                "positiveMassActiveCoordinateWeightNegative",
                "The positive-mass sign theorem applies to the defining property of each active subtype element."),
            TheoremNode("active-coordinate-quadratic-is-strictly-negative",
                "active_coordinate_quadratic_neg",
                "The active-coordinate quadratic form is strictly negative",
                "nonzeroActiveCoordinateVectorHasNegativeQuadraticValue",
                "Every summand is nonpositive and a nonzero coordinate supplies one strictly negative summand."),
            TheoremNode("exact-transport-gives-negative-target-value",
                "exact_transport_gives_negative_target_value",
                "Exact transport gives a negative target value",
                "exactTransportCarriesNegativeCoordinateQuadratic",
                "Substitution of the exact readout transfers strict negativity to the target quadratic domain."),
            TheoremNode("exact-transport-preserves-nonzero-vectors",
                "exact_transport_preserves_nonzero",
                "Exact transport preserves nonzero vectors",
                "injectiveTransportPreservesNonzero",
                "Injectivity prevents collapse of a nonzero active coordinate vector in the target space.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/Pick/ObserverSignedSupportBarcode")),
        ]));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id, string declaration, string heading, string formulaId, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(F.Disp(F.Id(formulaId))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);
}
