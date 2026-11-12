using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class PerfectPairingCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PerfectPairingCount.";

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cardinalities and evaluations of perfect pairings on finite label sets.",
        H("Perfect pairing count"),
        Blocks(
            Paragraph(Text(
                "Let alpha be a finite type with decidable equality. A perfect pairing of a finite label set U "
                + "is a finite set P of pairwise disjoint two-element label sets whose union is U. "
                + "Write p(U) for the number of these perfect pairings. The empty set has one perfect pairing.")),
            Entry("pairing-support-card", "pairingSupport_card", "Cardinality of a partial pairing support",
                "For every partial pairing P of U, the cardinality of pairingSupport(P) equals twice the cardinality of P. "
                + "The disjoint-union cardinality formula sums the cardinality two of every edge."),
            Entry("perfect-pairing-card", "card", "Number of edges in a perfect pairing",
                "If P is a perfect pairing of U, then the cardinality of U equals twice the cardinality of P."),
            Entry("pairing-polynomial-rank-one", "finitePairingPolynomial_rankOne", "Rank-one edge evaluation",
                "Let x be a real weight on labels and let c be a real weight on finite label sets. "
                + "Assume c(e) is the product of x(i) over labels i in e whenever e has cardinality two. "
                + "Then finitePairingPolynomial(U,c) equals p(U) times the product of x(i) over all labels i in U. "
                + "Each perfect pairing partitions U, so each label occurs exactly once in its product."),
            Entry("pairing-polynomial-constant", "finitePairingPolynomial_const", "Constant edge evaluation",
                "Let kappa be real and assume c(e) equals kappa whenever e has cardinality two. "
                + "Then finitePairingPolynomial(U,c) equals p(U) times kappa to the power floor(cardinality(U)/2). "
                + "Every perfect pairing has exactly cardinality(U)/2 edges; for odd cardinality the sum is empty."),
            Entry("perfect-pairing-count-rec", "perfectPairingCount_rec", "Recursion by the partner of a label",
                "For a label a in U, p(U) is the sum over b in U with a removed of p(U with a and b removed). "
                + "A perfect pairing has a unique edge containing a. Remove that edge and record the other endpoint b. "
                + "Conversely, insert the edge with endpoints a and b into a perfect pairing of the remaining labels. "
                + "The residual support excludes both endpoints, so these constructions are mutually inverse."),
            Entry("perfect-pairing-count", "perfectPairingCount", "Double-factorial count",
                "If the cardinality of U is even, p(U) equals the double factorial of (cardinality(U) minus one), "
                + "where natural subtraction gives zero in the empty case. If the cardinality is odd, p(U) equals zero. "
                + "The even formula follows by induction using the partner recursion and its cardinality(U) minus one possible partners. "
                + "The odd case follows because every perfect pairing covers twice its number of edges. "
                + "In particular, a four-element label set has three perfect pairings and a six-element label set has fifteen."))));
}
