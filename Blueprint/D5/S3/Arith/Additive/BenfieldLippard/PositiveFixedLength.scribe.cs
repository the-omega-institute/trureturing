using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive.BenfieldLippard;

internal sealed class PositiveFixedLengthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/BenfieldLippard/PositiveFixedLength.";
    private static readonly LibraryNoteRef Supplier =
        LibraryNoteRef.Create("D5/L/AdditiveNumberTheory/waringformalization2026lean");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For each exponent at least two, a fixed positive length represents every sufficiently large natural number.",
        H("Fixed-length positive power sums"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("eventual-fixed-length"),
                DeclarationHandle.Create(Prefix + "eventual_fixed_length"),
                H("A fixed positive length"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Supplier),
                Blocks(
                    Paragraph(Text(
                        "Let g be the uniform Waring bound for the exponent k. "
                        + "Put a = 2^k − 1, m = a^(k−1), and R = m·2^k. "
                        + "A block of m twos and a block consisting of a followed by m ones both contribute R, and their lengths differ by one.")),
                    Paragraph(Text(
                        "Apply the Waring bound after reserving g copies of R and one extra one. "
                        + "If i positive bases survive removal of zeros, append i short blocks, g−i long blocks and the extra one. "
                        + "This gives a representation of length g(m+1)+1, independent of the target."))
                ),
                DescribeRole.Theorem)
        )));
}
