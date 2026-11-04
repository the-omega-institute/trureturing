using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Hypercube;

internal sealed class RROTailLinearLengthSetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Boolean cube admits linear-length disjoint terminal fibres with edge contacts.",
        H("RRO Tail Linear-Length Sets"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rro-tail-linear-length-sets"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Hypercube/RROTailLinearLengthSets.proposition_36_1"),
                H("Linear-length fibres and edge contacts"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive k, take the Boolean k-cube. Its edge set has "
                            + "k·2^(k−1) elements, while prefixes of length "
                            + "k−1+ceil(log₂ k) have at least that many values. An "
                            + "injective prefix assignment therefore labels every edge.")),
                    Paragraph(Text(
                        "At a vertex, attach to each incident edge the assigned prefix and "
                            + "a final bit determined by a fixed total ordering of the two "
                            + "endpoints. The resulting fibre has exactly k words; distinct "
                            + "fibres are disjoint because equal prefixes identify an edge "
                            + "and the two endpoint bits are opposite.")),
                    Paragraph(Text(
                        "Each cube edge contributes one word to each endpoint fibre with a "
                            + "common prefix and opposite final bits, exactly the contact relation "
                            + "defined in Lean. The word length is "
                            + "(k−1+ceil(log₂ k))+1 = k+ceil(log₂ k).")),
                    Paragraph(Text(
                        "This theorem establishes the fibre construction and edge contacts. "
                            + "It does not establish metric, separator, causality, or finite-search "
                            + "claims from the surrounding source."))),
                DescribeRole.Theorem))));
}
