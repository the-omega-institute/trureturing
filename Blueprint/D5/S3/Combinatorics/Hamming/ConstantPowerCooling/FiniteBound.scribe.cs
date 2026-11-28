using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming.ConstantPowerCooling;

internal sealed class FiniteBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hamming/ConstantPowerCooling/FiniteBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The clique-packing leave bounds the number of cooling-code information classes.",
        H("The finite cooling-code upper bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-cpecc-upper-bound"),
                DeclarationHandle.Create(Prefix + "finite_cpecc_support_upper_bound"),
                H("The finite cooling-code upper bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc")),
                Blocks(Paragraph(Text("Let V be a finite point set of cardinality n, and let P be a finite indexed family of information classes. Each word is a w-subset, each deletion of t points misses a word in every class, and words in different classes meet in at most one point. Put k = w + t. Assume k ≤ n, 1 ≤ t, t + 3 < w, 1 ≤ g < w, k − 1 divides n − g, k(k − 1) divides n(n − g), and k(k + g − 2) ≤ 2B(w,t). Then the number of classes is at most J = n(n − g)/(k(k − 1)). Write R = (n − g)/(k − 1). Choose one k-clique from each of the b shadows with such a clique. If a point is covered r times, its leave degree is (g − 1) + (k − 1)(R − r). The remaining shadows live on points with R − r positive, since their support degrees are at least w − 1. Summing the deficits gives k(J − b), so twice the edge count of the induced leave is at most k(k + g − 2)(J − b). The Appendix A threshold pays for each remaining shadow."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("two-point-matching-leave"),
                DeclarationHandle.Create(Prefix + "g2_optimal_support_clique_packing"),
                H("Equality and the two-point matching leave"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc")),
                Blocks(Paragraph(Text("With g = 2 and k² < 2B(w,t), equality in the finite upper bound gives a k-clique in every class shadow. If the deficit d = J − b were positive, the remaining d shadows would use at least dB(w,t) edges, while the induced leave would have fewer. Thus d = 0, every incidence deficit vanishes, and the ambient leave of the selected cliques has degree one everywhere. It is a perfect matching."))), DescribeRole.Theorem)),
        []));
}
