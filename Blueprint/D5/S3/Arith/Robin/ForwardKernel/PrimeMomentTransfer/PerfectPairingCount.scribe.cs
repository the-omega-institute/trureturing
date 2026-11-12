using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class PerfectPairingCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.";

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cardinalities and evaluations of perfect and partial pairings on finite label sets.",
        H("Perfect pairing count"),
        Blocks(
            Paragraph(Text(
                "Let alpha be a finite type with decidable equality. A perfect pairing of a finite label set U "
                + "is a finite set P of pairwise disjoint two-element label sets whose union is U. "
                + "Write p(U) for the number of these perfect pairings. The empty set has one perfect pairing.")),
            Entry("perfect-pairing-card", "IsPerfectPairing.card", "Number of edges in a perfect pairing",
                "The Lean declaration IsPerfectPairing.card states that if P is a perfect pairing of U, "
                + "then the cardinality of U equals twice the cardinality of P."),
            Entry("pairing-polynomial-rank-one", "finitePairingPolynomial_rankOne", "Rank-one edge evaluation",
                "Let x be a real weight on labels and let c be a real weight on finite label sets. "
                + "Assume c(e) is the product of x(i) over labels i in e whenever e has cardinality two. "
                + "Then finitePairingPolynomial(U,c) equals p(U) times the product of x(i) over all labels i in U. "
                + "Each perfect pairing partitions U, so each label occurs exactly once in its product."),
            Entry("pairing-polynomial-constant", "finitePairingPolynomial_const", "Constant edge evaluation",
                "Let kappa be real and assume c(e) equals kappa whenever e has cardinality two. "
                + "Then finitePairingPolynomial(U,c) equals p(U) times kappa to the power floor(cardinality(U)/2). "
                + "Every perfect pairing has exactly cardinality(U)/2 edges; for odd cardinality the sum is empty."),
            Entry("perfect-pairing-count", "perfectPairingCount", "Double-factorial count",
                "If the cardinality of U is even, p(U) equals the double factorial of (cardinality(U) minus one), "
                + "where natural subtraction gives zero in the empty case. If the cardinality is odd, p(U) equals zero. "
                + "A perfect pairing corresponds bijectively to the fixed-point-free involution on U that exchanges the endpoints of each edge. The inverse sends an involution sigma to its set of two-cycles {x,sigma(x)}. The even formula applies the existing cycle-type count card_fixedPointFreeInvolution and simplifies its factorial quotient by the even double-factorial identity. "
                + "The odd case follows because every perfect pairing covers twice its number of edges. "
                + "In particular, a four-element label set has three perfect pairings and a six-element label set has fifteen."),
            Entry("partial-pairing-count", "partialPairingCount", "Counting partial pairings",
                "For every finite label set U and natural p, the number of partial pairings of U with p edges "
                + "equals choose(cardinality(U),2p) times (2p-1)!!. The empty pairing is included. "
                + "The support of such a pairing has cardinality 2p, and its edges form a perfect pairing of the support. "
                + "Conversely, a perfect pairing of a 2p-element subset of U is a partial pairing of U with p edges. "
                + "Summing the perfect-pairing count over all possible supports gives the formula."))));
}
