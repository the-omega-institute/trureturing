using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PermutationSquare;

internal sealed class PermutationSquareEnumerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PermutationSquare/PermutationSquareEnumeration.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Dynamics/archer2026pattern");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Closed-form counts of indecomposable square-avoiders, the threshold of the conjectured recurrence, rational generating series over the integers, and the order-seven linear recurrence.",
        H("Enumeration, generating series, and linear recurrence"),
        Blocks(
            Node("permutationsquareenumeration-bounded-compositions-definition", "Compositions into parts at most four", "boundedCompositions", "For every nonnegative n, boundedCompositions(n) is the set of lists of natural numbers whose entries each lie between one and four inclusive and sum to n.", DescribeRole.Definition),
            Node("permutationsquareenumeration-c-definition", "Tetranacci composition count", "c", "For every nonnegative n, c(n) is the cardinality of boundedCompositions(n), counting the compositions of n into parts of size one, two, three, or four.", DescribeRole.Definition),
            Node("permutationsquareenumeration-series-b-definition", "Generating series of indecomposable square-avoiders", "seriesB", "The formal power series over the integers whose coefficient of X to the n equals b(n) for every nonnegative integer n.", DescribeRole.Definition),
            Node("permutationsquareenumeration-series-a-definition", "Generating series of nonempty square-avoiders", "seriesA", "The formal power series over the integers with zero constant term whose coefficient of X to the n equals a(n) for every positive integer n.", DescribeRole.Definition),
            Node("permutationsquareenumeration-indecomposable-count-and-recurrence-boundary-theorem", "Exact indecomposable counts, composition convolution, and recurrence threshold", "indecomposable_count_and_recurrence_boundary", "The sequence b(n) equals zero at n equal to zero, takes the values 1, 1, 2, 3, 3, 5, 6, 7 for n from one through eight, and equals floor(n / 2) plus four for every n at least nine. With c(0) equal to one, for every positive n the total count a(n) equals the convolution sum over k from one through n of b(k) times c(n minus k). For every n at least five, a(n) satisfies a(n) = a(n - 1) + a(n - 2) + a(n - 3) + a(n - 4) + b(n), so for every n at least six the identity a(n) = a(n - 1) + a(n - 2) + a(n - 3) + a(n - 4) + (n - 1) holds if and only if b(n) equals n minus one. Because b(n) equals n minus one for every n from six through ten and b(n) is strictly less than n minus one for every n at least eleven, for n at least six the identity a(n) = a(n - 1) + a(n - 2) + a(n - 3) + a(n - 4) + (n - 1) holds if and only if n is at most ten, whereas for every n at least eleven a(n) is strictly less than a(n - 1) + a(n - 2) + a(n - 3) + a(n - 4) + (n - 1).", DescribeRole.Theorem),
            Node("permutationsquareenumeration-generating-series-and-order-seven-recurrence-theorem", "Rational generating series and the order-seven recurrence", "generating_series_and_order_seven_recurrence", "Let num be X + X^4 - X^5 + X^6 + X^7 - X^8 - X^11, let denB be (1 - X)(1 - X^2), let denC be 1 - X - X^2 - X^3 - X^4, and let denA be the product denB times denC in formal power series over the integers. Both seriesB and seriesA have constant coefficient zero; denB, denC, and denA are units in the ring of integer formal power series; seriesA times denC equals seriesB so seriesA equals seriesB times the inverse of denC; seriesB times denB equals num so seriesB equals num times the inverse of denB; seriesA times denA equals num so seriesA equals num times the inverse of denA; denA expands to 1 - 2X - X^2 + 2X^3 + X^5 - X^7; and for every n at least twelve, over the integers, a(n) equals 2a(n - 1) + a(n - 2) - 2a(n - 3) - a(n - 5) + a(n - 7).", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
