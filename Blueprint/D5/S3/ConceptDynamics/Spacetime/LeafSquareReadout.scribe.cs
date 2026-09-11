using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class LeafSquareReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-leaf source filtering of the actual generated history gives a finite square sum.",
        H("Leaf Source Square Readout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("literal-source-filter"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.sourceFilter"),
                H("Selection filtering preserves the complete context"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Definition 13 permits any fixed set of source trees. The filter changes only the selected "
                    + "events, retaining the identical archive, current region, attributes and causal data. "
                    + "The balanced lift reuses the input balance proof."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-charge-coefficients"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.source_charge_apply"),
                H("One finitely supported charge records signed source fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The charge is the finite sum of signed singletons over actual selected occurrences. "
                    + "Its coefficient is the full signed event-fiber sum and the singleton-filter readout. "
                    + "A zero coefficient can still have a nonempty occurrence fiber."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-filtered-product-fibers"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_product_fiber_readout"),
                H("The generated history contains every ordered selected parent pair"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The fixed filter admits precisely pairs of equal leaf sources. Complete occurring fibers "
                    + "are grouped before any zero total is discarded. Distinct occurrences with the same leaf "
                    + "source contribute cross terms; equal nonleaf sources are excluded."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("leaf-square-readout"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_square_readout"),
                H("The actual readout equals the leaf-source square sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem consumes both representation equalities and finite distributivity. It holds "
                    + "for every balanced history in dimension three, including empty selections and signed "
                    + "cancellation, without positivity or per-source balance assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("natural-leaf-square-readout"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/LeafSquareReadout.leaf_square_readout_nat"),
                H("Natural leaf indices reindex the same finite sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Natural leaf charges are derived from the one source charge by restriction and precomposition. "
                    + "Restriction to leaves precedes the support bijection. This establishes only the readout "
                    + "identity in Proposition 68.1, with no syntax-membership, separation, whole-CSA or "
                    + "ZFC conservativity or consistency claim."))),
                DescribeRole.Theorem))));
}
