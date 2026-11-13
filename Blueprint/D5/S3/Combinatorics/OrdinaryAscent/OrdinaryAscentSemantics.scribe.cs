using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.OrdinaryAscent;

internal sealed class OrdinaryAscentSemanticsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/OrdinaryAscent/OrdinaryAscentSemantics.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/mazhang2026ordinary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal ordinary ascent words, actual admissible ranks and the Catalan-pair construction, with its precise carrier and boundary conditions.",
        H("Ordinary ascent Semantics"),
        Blocks(
            Node("Pattern", "Pattern", "Pattern",
                "The thirteen reduced patterns 00-0, 00-1, 01-0, 01-1, 01-2, 02-1, 10-0, 10-1, 10-2, 11-0, 12-0, 20-1 and 21-0.", DescribeRole.Definition),
            Node("Fits", "Fits", "Fits",
                "The literal equalities and strict inequalities defining each of the thirteen patterns on three nonnegative values.", DescribeRole.Definition),
            Node("Contains", "Contains", "Contains",
                "There exist indices i,i+1,k with i+1<k<length, and the values at those positions fit the indicated literal pattern. The first two positions are adjacent.", DescribeRole.Definition),
            Node("IsAscent", "IsAscent", "IsAscent",
                "At position zero the value is zero. At each later position the value is at most one plus the strict adjacent-ascent count of the preceding prefix. Empty words are included.", DescribeRole.Definition),
            Node("avoiders", "avoiders", "avoiders",
                "The set of words of the stated length satisfying the ordinary ascent bound and avoiding every pattern in the given finite set.", DescribeRole.Definition),
            Node("Primitive", "Primitive", "Primitive",
                "Adjacent values are unequal. This imposes no pairwise distinctness of all values.", DescribeRole.Definition),
            Node("contains-append-iff", "contains append iff", "contains_append_iff",
                "Appending one letter preserves the old occurrences and creates exactly the occurrences that use the appended value as the third entry of an earlier adjacent pair.", DescribeRole.Theorem),
            Node("ascent-take", "ascent take", "ascent_take",
                "Every initial segment of an ordinary ascent sequence is an ordinary ascent sequence, including empty and oversize takes.", DescribeRole.Theorem),
            Node("ascent-append-iff", "ascent append iff", "ascent_append_iff",
                "A one-letter extension is ordinary precisely when the prefix is ordinary and the new letter is zero for an empty prefix, or at most one plus its ascent count otherwise.", DescribeRole.Theorem),
            Node("asc-le", "asc le", "asc_le",
                "The strict adjacent-ascent count is at most length minus one, with natural subtraction handling the empty word.", DescribeRole.Theorem),
            Node("asc-append", "asc append", "asc_append",
                "For an empty prefix the new ascent contribution is zero. Otherwise it is one exactly when the previous final value is strictly smaller than the appended letter.", DescribeRole.Theorem),
            Node("entry-le-asc", "entry le asc", "entry_le_asc",
                "Every actual entry of an ordinary ascent sequence is at most its total number of strict adjacent ascents.", DescribeRole.Theorem),
            Node("ascent-isInversionSeq", "ascent isInversionSeq", "ascent_isInversionSeq",
                "An ordinary ascent sequence satisfies the existing zero-based inversion-sequence bounds, value at index i at most i. No converse or avoidance transfer is asserted.", DescribeRole.Theorem),
            Node("avoiders-finite", "avoiders finite", "avoiders_finite",
                "At every finite length and for every finite forbidden-pattern set, the actual ordinary avoiding-word set is finite.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(("ordinaryascentsemantics-" + id).ToLowerInvariant()), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
