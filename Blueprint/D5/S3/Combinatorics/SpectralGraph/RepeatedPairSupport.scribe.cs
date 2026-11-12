using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;
internal sealed class RepeatedPairSupportDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/idealintersection2026sixsupport");
    private static DocumentBlock Item(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create("D5/S3/Combinatorics/SpectralGraph/RepeatedPairSupport." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete repeated-pair support operator for every finite tail index set.",
        H("General-index paired support and the actual ideal graph"),
        Blocks(
            Paragraph(Text("The source is the repeated-pair-product-tail note at PR9 revision 6d491f77b35dec808fc777b69939c56cdae5dc02, blob 66664013207b88567bf74f1a9a0c6eaf65d07f24. This module proves the full invariant embedding, with every support and arbitrary finite tail. Its operator is represented in the subset basis; no principal-compression eigenvalue claim is used. The existing four-index lift retains its original scope. The product-tail spectral criterion, its equality requirement of at least two tail coordinates, general Q3, and the three-prime integral-block boundary are separate obligations.")),
            Item("sum-four", "sum_four", "All four paired-coordinate sectors",
                "The complete finite-index sum decomposes into the four possibilities for the two paired coordinates and every remaining support. The full squarefree alternating operator proof consumes this shared helper."),
            Item("disjoint-sum", "disjoint_sum", "Disjointness on both coordinate sectors",
                "Disjointness of two full disjoint-union supports is equivalent to disjointness in both coordinate sectors. This helper is consumed by the full alternating support action."),
            Item("paired-value-sum", "pairedValue_sum", "Paired values on all full supports",
                "Every paired function value on a disjoint-union support has its exact sign in the two singleton sectors and vanishes in the other sectors; the actual squarefree invariant lift consumes this helper."),
            Item("weighted-symmetry", "weighted_symmetry", "Weighted symmetry on the whole tail",
                "For every finite tail and every real parameter, the full subset matrix becomes Hermitian after multiplication by the diagonal product weights. This statement does not assert positivity when weights vanish or are negative."),
            Item("zero-sum", "paired_lift_sum", "Cancellation on the entire vertex set",
                "For all positive natural exponents and every tail function, equal paired support weights make its full exponent-box lift sum to zero. Empty and full supports and every zero-valued cell are included."),
            Item("nonzero", "paired_lift_nonzero", "A nonzero actual lift",
                "Every nonzero tail function has a nonzero graph lift for all positive natural exponents. The proof produces an actual proper nonempty support and invokes the complete support-fiber theorem."),
            Item("action", "paired_support_action", "The complete invariant action",
                "For every support and every natural exponent, the complement support operator acts on paired values by K minus the identity. The proof treats all four possibilities for the two repeated coordinates and the entire powerset of the arbitrary tail."),
            Item("actual-eigenvalue", "actual_paired_eigenvalue", "Transport to actual ideals",
                "For every finite tail, distinct primes, positive natural exponents, and nonzero full K eigenvector, V+1-e is an eigenvalue of the actual nonzero-proper-ideal intersection graph. V=(a+1)^2 product(k_i+1)-2. The proof consumes nonzero and weighted-zero-sum evidence and the actual ideal/support isomorphism; it does not assume that a compression eigenvector is a graph eigenvector.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/SpectralGraph/IdealIntersectionObstructions"))]));
}
