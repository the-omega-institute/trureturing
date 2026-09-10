using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class FiniteGraphEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Structural finite graphs reconstruct functions on exactly their archived domain.",
        H("Finite Graph Reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-graph-code-equivalence"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/FiniteGraphEncoding.graph_code_equiv"),
                H("Exact functions and legal HF graphs"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The independent graph predicate requires totality and a unique legal value at each archived "
                    + "input, and excludes every other entry. Decoding chooses that unique value only on the "
                    + "finite domain. The representation uses the proved equivalence for its value carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("legal-graph-complete-reconstruction"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/FiniteGraphEncoding.encode_decodeGraph"),
                H("Reconstruction loses no graph entries"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Unique lookup recovers every member of a legal graph. Extensional HF equality proves "
                    + "the reverse round trip. The module also represents arbitrary relations with archived "
                    + "endpoints and arbitrary subsets of the archive, each with both round trips."))),
                DescribeRole.Theorem))));
}
