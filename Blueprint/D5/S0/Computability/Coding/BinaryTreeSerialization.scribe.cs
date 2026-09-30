using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class BinaryTreeSerializationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A recursive binary parser recovers each tagged FreeMagma tree and its unused suffix.",
        H("Recursive Binary Tree Serialization"),
        Blocks(
            Paragraph(Text(
                "The two leaf atoms are encoded by false,false and false,true. A branch is "
                    + "marked by true and followed by the complete encodings of its two children. "
                    + "The parser consumes one complete tree code and returns the remaining suffix.")),
            Describe.Lean(
                DescribeId.Create("binary-tree-suffix-recovery"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/BinaryTreeSerialization.serialization_spec"),
                H("Exact suffix-preserving recursive parsing"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every tagged FreeMagma tree and every suffix, parsing the concatenated "
                        + "code and suffix reconstructs the tree and returns exactly that suffix. "
                        + "Injectivity, prefix freedom, and empty-suffix decoding are residual "
                        + "corollaries and are not separate claims here."))),
                DescribeRole.Theorem))));
}
