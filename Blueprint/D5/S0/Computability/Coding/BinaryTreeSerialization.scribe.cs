using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Coding;

internal sealed class BinaryTreeSerializationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A recursive binary parser recovers each tagged FreeMagma tree and its unused suffix.",
        H("Recursive Binary Tree Serialization"),
        Blocks(
            Paragraph(Text(
                "The two leaf atoms are encoded by the two words false,false and false,true. "
                    + "A branch is marked by true and followed by the complete encodings of its "
                    + "two children. The parser consumes one complete tree code and returns the "
                    + "remaining suffix.")),
            Describe.Lean(
                DescribeId.Create("binary-tree-serialization-spec"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Coding/BinaryTreeSerialization.serialization_spec"),
                H("Exact recursive parsing and a prefix-free injective code"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Parsing an appended suffix reconstructs the original tree and preserves that "
                        + "suffix. Equal codes therefore give equal trees, and a complete code "
                        + "cannot be a proper prefix of another complete code. Parsing a code with "
                        + "an empty suffix gives the decoder round trip."))),
                DescribeRole.Theorem))));
}
