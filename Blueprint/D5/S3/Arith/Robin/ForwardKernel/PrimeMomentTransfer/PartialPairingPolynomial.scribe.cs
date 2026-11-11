using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class PartialPairingPolynomialDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/PartialPairingPolynomial.";

    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite perfect pairing polynomials and their expansion over partial pairings.",
        H("Partial pairing polynomial"),
        Blocks(
            Paragraph(Text(
                "Let alpha be a finite label type with decidable equality and let U be a finite set of labels. "
                + "Edges are finite label sets, so no orientation, ordering, or repeated edge is introduced. "
                + "This is the arbitrary-order combinatorial form of the pairing expansion underlying the four-label perfectPairingSum.")),
            Entry("pairing-support", "pairingSupport", "Labels covered by edges",
                "For a finite set P of finite label sets, pairingSupport(P) is the union of its members.", DescribeRole.Definition),
            Entry("is-partial-pairing", "IsPartialPairing", "Partial pairing",
                "IsPartialPairing(U,P) means that every edge of P has exactly two labels, distinct edges in P are disjoint, "
                + "and the union of the edges is a subset of U.", DescribeRole.Definition),
            Entry("is-perfect-pairing", "IsPerfectPairing", "Perfect pairing",
                "IsPerfectPairing(U,P) means that P is a partial pairing of U and the union of its edges equals U. "
                + "In particular, the empty pairing is a perfect pairing of the empty label set.", DescribeRole.Definition),
            Entry("finite-pairing-polynomial", "finitePairingPolynomial", "Perfect pairing polynomial",
                "For an edge weight c valued in the reals, finitePairingPolynomial(U,c) is the sum over all perfect pairings P of U "
                + "of the product over edges e in P of c(e). The empty product equals one.", DescribeRole.Definition),
            Entry("finite-pairing-polynomial-add", "finitePairingPolynomial_add", "Expansion over a partial pairing",
                "For every finite label type alpha, finite label set U, and real edge weights c,d, "
                + "finitePairingPolynomial(U,e mapped to c(e)+d(e)) equals the sum over partial pairings P of U of "
                + "the product of c(e) over e in P, multiplied by finitePairingPolynomial(U minus pairingSupport(P),d). "
                + "Expand the product on each perfect pairing M by its edge subsets P. "
                + "The map (M,P) to (P,M minus P) is a bijection onto a partial pairing and a perfect pairing of its uncovered labels. "
                + "The inverse takes (P,Q) to (P union Q,P); the disjoint label supports imply disjoint edge sets. "
                + "Thus each contribution occurs exactly once, with no factorial factor.", DescribeRole.Theorem))));
}
