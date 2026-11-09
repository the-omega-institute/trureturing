using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class BlitvicKammounSteingrimsson14325CoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed 14325 comparisons force the first and last ranks for every positive packing size.",
        H("Exact source structure of 14325 packings"),
        Blocks(
            Paragraph(Text("The zero-based pattern is (0,3,2,1,4), overlap is two, "
                + "and stride is three. The source length 5+(j−1)·3 equals 3j+2 for "
                + "j≥1. Packs is the existing predicate requiring every strict pairwise "
                + "comparison in every prescribed window. There is no avoidance "
                + "condition or quotient, and extra occurrences are allowed.")),
            Paragraph(Text("Write aₜ for position 3t, bₜ for position 3t+1, and cₜ "
                + "for position 3t+2. Window t requires precisely "
                + "aₜ<aₜ₊₁<cₜ<bₜ<bₜ₊₁. The private packing_chain_iff proves both "
                + "directions of this comparison translation. The private chain_bounds "
                + "then proves by induction on the number of windows that every "
                + "position lies between a₀ and bⱼ in rank.")),
            Node("packing_bounds", "Bounds for every rank assignment",
                "For every natural j≥1, every rank function w satisfying Packs, and "
                + "every position x, w(0)≤w(x)≤w(3j+1). Injectivity is not required. "
                + "Appending a window adds three positions, and its chain orders all "
                + "three between the old lower endpoint and the new upper endpoint."),
            Node("packing_extrema", "Forced ranks in actual source permutations",
                "For every natural j≥1 and every actual permutation w satisfying "
                + "Packs, w(0)=0 and w(3j+1)=3j+1. Surjectivity supplies a position "
                + "with rank zero and one with the greatest rank; packing_bounds "
                + "forces the two endpoint equalities. Thus deleting these endpoints "
                + "removes two forced ranks, without any symmetry or labeling factor."),
            Paragraph(Text("The remaining grid has xₜ=aₜ₊₁<yₜ=cₜ<zₜ=bₜ, with "
                + "increasing x and z chains. An exact rank-assignment/grid bijection "
                + "and first-z insertion/deletion bijection are still required to "
                + "identify the actual cardinality with the transfer rows. The present "
                + "theorems prove endpoint constraints and do not claim that cardinality "
                + "identity, either modular conclusion, or completion of issue 28504.")))));

    private static DocumentBlock Node(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("bks14325-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(new Formula.Apply(F.Id(name), [F.Id("j"), F.Id("w")]))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
