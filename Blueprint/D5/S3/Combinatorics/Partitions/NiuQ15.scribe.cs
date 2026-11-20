using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class NiuQ15Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/NiuQ15.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/PermutationPatterns/niu2026firstdescent");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact uniform first-descent probabilities and the limiting law for every rectangular row count at least two.",
        H("Niu Question 15 for Rectangular Tableaux"),
        Blocks(
            Node("niuq15-eventprobability", "Uniform event probability", "eventProbability",
                "The probability of an event on the finite sample is the number of tableaux in the event divided by the number of tableaux in the sample.",
                DescribeRole.Definition),
            Node("niuq15-rectangledescent", "Rectangle descent", "rectangleDescent",
                "The rectangle has K = k + 2 rows. For positive width the descent is the one-based second-row first entry minus one. At width zero the descent is extended by zero.",
                DescribeRole.Definition),
            Node("niuq15-rectangletailprobability", "Survival probability", "rectangleTailProbability",
                "At k, n and r, the uniform event is that the rectangle descent is at least r.",
                DescribeRole.Definition),
            Node("niuq15-rectanglepointprobability", "Point probability", "rectanglePointProbability",
                "At k, n and r, the uniform event is that the rectangle descent equals r.",
                DescribeRole.Definition),
            Node("niuq15-rectangleoddentryprobability", "Odd-entry probability", "rectangleOddEntryProbability",
                "At positive width, the event is that the one-based entry in row two and column one is odd, equivalently that the descent is even.",
                DescribeRole.Definition),
            Node("niuq15-card-standardtableau-eq-shiftedcount", "Straight-shape cardinality", "card_standardTableau_eq_shiftedCount",
                "For any weakly decreasing profile with at least two row slots, the rational cast of the tableau count equals the shifted Vandermonde formula. Both counts equal one at size zero. At positive size, they sum over the same removable row ends with the same shortened profiles. Strong induction on the number of cells gives equality.",
                DescribeRole.Theorem),
            Node("niuq15-exact-count-identity", "Rectangle and shortened-shape count identity", "ExactRectangleTailCount",
                "For K = k + 2, positive width n and r at most n, the shortened-shape count times the descending factorial of K n of length r equals the rectangle count times choose(r + K - 1, K - 1) times the descending factorial of n of length r.",
                DescribeRole.Definition),
            Node("niuq15-exactrectangletailcount", "Exact rectangle tail count", "exactRectangleTailCount",
                "The identity holds for every k. In the shifted Vandermonde product the upper-row factors are common. The factors involving the last row change from the integers 1 through K - 1 to the integers r + 1 through r + K - 1. Their ratio is the binomial coefficient. The size and last-row factorials give the two descending factorials.",
                DescribeRole.Theorem),
            Node("niuq15-finite-tail", "Exact survival probability", "rectangleTailProbability_eq",
                "At every positive width, the survival probability equals the finite survival function. For r at most n this follows from the count ratio and the prefix rotation. For r above n the event is empty.",
                DescribeRole.Theorem),
            Node("niuq15-finite-point", "Exact point probability", "rectanglePointProbability_eq",
                "At positive width, the point probability for r at most n is the survival probability times (K - 1) r (n + 1) / ((r + 1)(K n - r)). Above the width the point probability is zero.",
                DescribeRole.Theorem),
            Node("niuq15-rectanglequestion15", "First-descent law and odd-entry limit", "rectangleQuestion15",
                "For every K = k + 2 and each natural r, the survival probability tends to choose(r + K - 1, K - 1)/K^r and the point probability tends to r choose(r + K - 1, K - 2)/K^(r + 1). The limiting point masses sum to one. The probability of an odd second-row first entry tends to (K/(K + 1))^K. Prefix rotation and the count identity give the finite tails, and subtraction of adjacent tails gives the masses. Pairing adjacent tails and applying the common summable bound gives the parity limit.",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
