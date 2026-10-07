using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PermutationArrays;

internal sealed class DescentLexCountDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/hardin2013a222001");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-length three-column permutation arrays have count 2+(n+1)(n+2)(n+3)/6.",
        H("Three-column permutation arrays with compatible row orders"),
        Blocks(Describe.Lean(
            DescribeId.Create("a222001-positive-length-actual-array-count"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/PermutationArrays/DescentLexCount.count_arrays"),
            H("The count for every positive length"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("A row is an actual permutation of Fin 3. Its entry in column j "
                    + "is the natural number (r j).val+1, so the source symbols are exactly "
                    + "1,2,3. Adding one preserves strict comparisons, equality and non-strict "
                    + "comparisons. The descent count is the sum of the two indicators for "
                    + "entry 1 exceeding entry 2 and entry 2 exceeding entry 3. Lexicographic "
                    + "comparison tests the first entry, then the second, then the third.")),
                Paragraph(Text("The type Arrays n consists of functions from Fin n to these actual "
                    + "rows. The descent counts are nondecreasing along the original row indices, "
                    + "and the rows are lexicographically nonincreasing. Equal rows are allowed. "
                    + "For every n at least one, the cardinality is "
                    + "2+(n+1)*(n+2)*(n+3)/6, where the division is exact natural division.")),
                Paragraph(Text("In increasing lexicographic order the rows are 123,132,213,231,312,321, "
                    + "with descent counts 0,1,1,1,1,2. Descents therefore cannot increase when "
                    + "a row decreases lexicographically. The two array conditions force the "
                    + "descent count to be constant. Descent classes zero and two contain only "
                    + "123 and 321 respectively, giving exactly two constant arrays.")),
                Paragraph(Text("The middle class consists of all nonincreasing words on "
                    + "132,213,231,312. Their multisets preserve every occurrence, including "
                    + "repetitions. Sorting a multiset in decreasing order reconstructs the "
                    + "unique word. The equivalence between actual arrays and the disjoint sum "
                    + "of two constants and length-n multisets is exhaustive in both directions. "
                    + "Mathlib's Sym cardinality theorem counts the multisets by choosing n "
                    + "from n+3. Binomial symmetry and the descending factorial identity "
                    + "give the displayed cubic.")),
                Paragraph(Text("Positive length distinguishes the two constant arrays. "
                    + "At length zero there is one empty array; the displayed formula would "
                    + "give three. The theorem explicitly assumes n at least one. "
                    + "The cited OEIS entry publishes the formula as a conjecture. "
                    + "This statement concerns that exact array count, without an assertion "
                    + "about publication priority or external acceptance."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("oeis-a222001-descent-lex-arrays"),
                ResolutionKind.Proved)))));
}
