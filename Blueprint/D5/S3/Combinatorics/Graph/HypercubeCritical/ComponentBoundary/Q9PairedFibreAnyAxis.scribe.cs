using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9PairedFibreAnyAxisDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9PairedFibreAnyAxis";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The energy cost of three paired neighbours",
        H("Single fibres with three paired neighbours"),
        Blocks(Describe.Lean(
            DescribeId.Create("q9-paired-fibre-energy-three-contacts"),
            DeclarationHandle.Create(Module + ".triple_contact_card_le"),
            H("An upper bound on the three-contact single fibres"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Delete the main coordinate and fix a projected parity for the paired fibres. "
                    + "Each paired fibre has exactly four single neighbours. The two endpoints "
                    + "supply two neighbours each, and overlap would complete a selected square.")),
                Paragraph(Text(
                    "The switching signs give a function supported on the paired fibres. "
                    + "At a single fibre, the signed Huang terms agree, so a single fibre "
                    + "with k paired neighbours contributes k squared to the energy. "
                    + "The Huang square identity gives eight units per paired fibre. "
                    + "Subtracting the single-fibre energy from twice the incidence count "
                    + "shows that the number of one-contact fibres minus three times the number "
                    + "of three-contact fibres equals the nonnegative energy on empty fibres.")),
                Paragraph(Text(
                    "An order-preserving reindexing moves the main axis to the first coordinate "
                    + "and preserves the remaining fibre labels. The estimate applies to the "
                    + "selected apexes forced by opposite-parity witnesses in Hong, Wu and Xia's "
                    + "Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
            DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9OccupiedFibreParity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/HuangCubeCovariance")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Combinatorics/Graph/HypercubeCritical/CubicFiftyFourReconstruction"))
        ]));
}
