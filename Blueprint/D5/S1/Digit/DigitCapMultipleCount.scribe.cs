using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class DigitCapMultipleCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/DigitCapMultipleCount.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/dumont1999linearrecurrent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "With digit cap a·ell−1 the number of bounded-digit representations of n is the sum of "
            + "the cap a−1 counts of 0,…,⌊n/ell⌋.",
        H("Digit caps one below a multiple of the radix"),
        Blocks(
            Node("identity", "The multiple-cap identity", "count_multiple",
                "For ell≥2, a≥1 and every n, count (a·ell−1) ell n equals the sum of "
                + "count (a−1) ell t over 0≤t≤⌊n/ell⌋. Each digit d≤a·ell−1 splits uniquely as "
                + "d=ell·q+r with q≤a−1 and r<ell, so a representation of n splits into a "
                + "representation of t with digits at most a−1, where ell·t≤n, and a "
                + "representation of n−ell·t with digits below ell. The latter is the unique "
                + "ordinary radix expansion: there is at least one, and the quotient-digit bound "
                + "with q=1 allows at most one. So the representations of n with quotient "
                + "weight t correspond exactly to the cap a−1 representations of t. This is "
                + "Proposition 6.8 of Dumont, Sidorov and Thomas (1999).",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source)),
            Node("square", "The cap ell²−1", "count_square_sub_one",
                "For ell≥2, count (ell²−1) ell n=⌊n/ell⌋+1: with a=ell every summand is an "
                + "ordinary radix expansion count, equal to 1.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source)),
            Node("mono", "Monotone and nonconstant growth", "count_multiple_mono",
                "For a≥1 the counts with cap a·ell−1 are nondecreasing in n, because the sum "
                + "runs over the growing range 0,…,⌊n/ell⌋. For a≥2 the count at ell exceeds "
                + "the count at 0, since the extra summand counts the representation of 1 by "
                + "the single digit 1≤a−1. In particular, for ell≥3 the cap 2ell−1<ell²−1 "
                + "already gives nondecreasing, nonconstant counts.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("digit-cap-multiple-count-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), provenance,
            Blocks(Paragraph(Text(prose))), role);
}
