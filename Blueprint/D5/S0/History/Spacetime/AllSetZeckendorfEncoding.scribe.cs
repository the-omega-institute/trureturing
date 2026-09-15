using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Spacetime;

internal sealed class AllSetZeckendorfEncodingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All-Set Zeckendorf Encoding.",
        H("All-Set Zeckendorf Encoding"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("all-set-zeckendorf-encoding-injectivity"),
                DeclarationHandle.Create("D5/S0/History/Spacetime/AllSetZeckendorfEncoding.enc_injective_and_left_inverse"),
                H("Injectivity and decoding"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "In any universe, encode a finite von Neumann ordinal by tag zero paired with its "
                    + "finite Zeckendorf digit graph. Encode every other set by tag one paired with the "
                    + "set of encodings of its members. Membership recursion defines this map on all sets. "
                    + "Two encodings are equal if and only if their original sets are equal, and decoding "
                    + "the valid code of any set recovers that set. The natural number zero has an empty "
                    + "digit graph; positive words retain all positions, including their zero digits."))),
                DescribeRole.Theorem))));
}
