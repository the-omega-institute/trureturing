using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Nonnesting;

internal sealed class NonnestingBasicSumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Nonnesting/NonnestingBasicSum.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/elizalde2024pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Value cuts decompose doubled permutations into primitive direct-sum factors.",
        H("Direct Sums and Primitive Words"),
        Blocks(
            Node("nonnesting-nonnestingbasicsum-shift", "Shifted letters", "shift",
                "Shifting a word by m adds m to every letter.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicsum-directsum", "Direct sum of words", "directSum",
                "The direct sum appends a word shifted by m to a first word.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicsum-valuecut", "Value cut", "valueCut",
                "A cut at k splits a word after 2k positions, with only values at most k before the cut and only larger values after it.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicsum-primitive", "Primitive doubled word", "primitive",
                "A word of size n is primitive when it has no value cut strictly between zero and n.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicsum-sumindecomposable", "Indecomposable pattern", "sumIndecomposable",
                "At every nonempty proper split of a pattern, a letter on the right is at most a letter on the left.", DescribeRole.Definition),
            Node("nonnesting-nonnestingbasicsum-directsum-perm", "Direct sums preserve doubled support", "directSum_perm",
                "The direct sum of doubled permutations of sizes m and n is a doubled permutation of size m plus n.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasicsum-indecomposable-sublist-append", "An indecomposable occurrence lies on one side", "indecomposable_sublist_append",
                "An indecomposable pattern occurring across two value-separated blocks occurs wholly in one block.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasicsum-indecomposable-map", "Increasing relabeling preserves indecomposability", "indecomposable_map",
                "A strictly increasing relabeling of the positive letters of an indecomposable pattern remains indecomposable.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasicsum-occurs-directsum-iff", "Pattern occurrence in a direct sum", "occurs_directSum_iff",
                "For a positive indecomposable pattern using every letter in its range, occurrence in a direct sum is equivalent to occurrence in one summand.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasicsum-valuecut-split-perm", "Splitting a doubled permutation at a cut", "valueCut_split_perm",
                "A value cut of a doubled permutation yields two doubled permutations whose direct sum is the original word.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasicsum-first-primitive-factor", "Existence of a first primitive factor", "first_primitive_factor",
                "Every nonempty doubled permutation splits into an initial primitive factor and a remaining doubled permutation.", DescribeRole.Theorem),
            Node("nonnesting-nonnestingbasicsum-primitive-split-unique", "Uniqueness of a primitive split", "primitive_split_unique",
                "Two primitive initial-factor decompositions of the same doubled word have equal cut sizes and equal factors.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
