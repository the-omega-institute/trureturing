using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class WeaklyContractibleFactorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact factorization through a weakly contractible finite poset",
        H("Exact factorization through a weakly contractible finite poset"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-nullhomotopic-order-map-exact-factorization"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/WeaklyContractibleFactor.factors_through_weakly_contractible"),
            H("A nullhomotopic order map factors through a contractible order complex"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Let an order map between nonempty finite posets have nullhomotopic order-complex realization. There is a finite poset with contractible order complex, an order embedding of the source into it, and an order map from it to the target. Their composite equals the given order map. The chain-maximum projection is a homotopy equivalence on realizations. A finite extension of the constant fence and its mapping cylinder agree on a common lower row, so the relative deformation retract glues to a contraction of the factor realization."))),
            DescribeRole.Theorem))));
}
