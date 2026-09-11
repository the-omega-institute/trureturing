using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class ProductPathsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Generated Product Causality.",
        H("Generated Product Causality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("productpaths-edge"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ProductPaths.Edge"),
                H("Only copied and parent edges generate causality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The generating relation has precisely four constructors: copied left edges, copied right "
                    + "edges, and one edge from each parent to its generated child. Generated vertices have no "
                    + "outgoing generating edge."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("productpaths-path-to-left"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ProductPaths.path_to_left"),
                H("A path ending in an old component reflects old order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The predecessor component invariant is proved by induction on a nonempty path. Each last "
                    + "edge entering an old component has its predecessor there, and the original strict "
                    + "relation composes. The right-component theorem is symmetric. This invariant is used by "
                    + "the actual archive embeddings."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("productpaths-path-time"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Spacetime/ProductPaths.path_time"),
                H("Frozen strict-coordinate results prove path legality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two-parent maximum plus one makes each generating edge increase integer time. The "
                    + "frozen strict-coordinate path and acyclicity theorems apply directly. A separate path "
                    + "characterization identifies a generated event's ancestors as its parents and their old "
                    + "predecessors."))),
                DescribeRole.Theorem))));
}
