using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class ParryTopologicalEntropyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef SGapEntropy =
        LibraryNoteRef.Create("D5/L/TotalVariation/ahmadidastjerdijangjoo2013sgap");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Topological entropy of the native bilateral forbidden-run shift.",
        H("Topological entropy of the bilateral Parry shift"),
        Blocks(Describe.Lean(
            DescribeId.Create("parry-bilateral-topological-entropy"),
            DeclarationHandle.Create("D5/S3/TotalVariation/ParryTopologicalEntropy.bilateral_entropy"),
            H("The Perron root gives the topological entropy"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(SGapEntropy),
            Blocks(
                Paragraph(Text(
                    "For k at least two, take all Boolean paths on the integers for which "
                    + "every block of length k contains a false bit. With the product uniform "
                    + "structure, the one-step left shift restricted to this set has cover "
                    + "entropy log(beta_k), where beta_k is the order-k d-bonacci Perron root.")),
                Paragraph(Text(
                    "Every finite admissible word extends to a one-sided path by appending "
                    + "false bits. The number of words and the powers of beta_k satisfy the "
                    + "same recurrence. The initial values bound the counts between beta_k^n "
                    + "and 2^k times beta_k^n. Taking logarithms per step supplies the one-sided "
                    + "entropy through the symbolic prefix-growth theorem.")),
                Paragraph(Text(
                    "For each nonpositive integer endpoint, reading the forward tail from that "
                    + "endpoint maps the bilateral space onto the same one-sided subshift "
                    + "and intertwines the shifts. These pullback uniformities decrease as "
                    + "the endpoint moves to the left. Every product entourage belongs to "
                    + "one of them, which yields the bilateral entropy from the one-sided law."))),
            DescribeRole.Theorem))));
}
