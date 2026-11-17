using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.SymmetricExtensions;

internal sealed class BoseHyperedgeSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/SymmetricExtensions/BoseHyperedgeSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Higher-body Bose support propagation", H("Higher-body Bose support propagation"),
        Blocks(
            Paragraph(Text("I and L are finite register and local-label types. All traces are the actual unnormalized tensor partial traces. Hansenne-Xu-Kraft-Guehne own the marginal-to-global support mechanism; the supplied application note is by Haobo Ma and Wenlin Zhang, in that order.")),
            Describe.Lean(DescribeId.Create("bosehyperedgesupport-subsystem-support"),
                DeclarationHandle.Create(Prefix + "subsystem_support"),
                H("subsystem support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Bose-supported actual subsystem marginal of a positive operator forces support of that operator under the lifted subsystem projector. The proof uses positive trace duality and the existing zero-weight support face, including singular and zero operators."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bosehyperedgesupport-pairs-of-subsystem-support"),
                DeclarationHandle.Create(Prefix + "pairs_of_subsystem_support"),
                H("pairs of subsystem support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every ordered pair inside a Bose-supported subsystem marginal has actual pair-Bose support. No product-state or diagonal-state premise is imposed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bosehyperedgesupport-hyperedgegraph"),
                DeclarationHandle.Create(Prefix + "hyperedgeGraph"),
                H("hyperedgeGraph"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two distinct registers are adjacent exactly when they lie together in one of the selected subsets. Empty and singleton subsets add no edge."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("bosehyperedgesupport-support-of-connected-hyperedges"),
                DeclarationHandle.Create(Prefix + "support_of_connected_hyperedges"),
                H("support of connected hyperedges"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If this union-of-cliques graph is connected and every selected subsystem marginal is Bose-supported, positivity gives full Bose support and equality of all ordered pair marginals. The result allows arbitrary finite selected families and retains uncovered and isolated-register boundaries through the graph hypothesis."))),
                DescribeRole.Theorem))));
}
