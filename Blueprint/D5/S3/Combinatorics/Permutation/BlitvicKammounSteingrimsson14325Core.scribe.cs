using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class BlitvicKammounSteingrimsson14325CoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Permutation/BlitvicKammounSteingrimsson14325Core.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/blitvickammounsteingrimsson2026patterns");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The prescribed 14325 permutations correspond exactly to rank assignments on the endpoint-deleted grid.",
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
            Node("packing_bounds", "Bounds for every rank assignment", BoundsFormula(),
                "For every natural j≥1, every rank function w satisfying Packs, and "
                + "every position x, w(0)≤w(x)≤w(3j+1). Injectivity is not required. "
                + "Appending a window adds three positions, and its chain orders all "
                + "three between the old lower endpoint and the new upper endpoint."),
            Node("packing_extrema", "Forced ranks in actual source permutations", ExtremaFormula(),
                "For every natural j≥1 and every actual permutation w satisfying "
                + "Packs, w(0)=0 and w(3j+1)=3j+1. Surjectivity supplies a position "
                + "with rank zero and one with the greatest rank; packing_bounds "
                + "forces the two endpoint equalities. Thus deleting these endpoints "
                + "removes two forced ranks, without any symmetry or labeling factor."),
            Node("count_eq_grid", "Exact cardinality after removing endpoints", CountFormula(),
                "For every natural j≥1, the actual count equals the number of grid "
                + "rank assignments. GridPacking consists of permutations q of 3j "
                + "ranks, indexed so that q(3t+2), q(3t+1), q(3t) are xₜ, yₜ, zₜ. "
                + "Each column satisfies xₜ<yₜ<zₜ, and both x and z increase across "
                + "successive columns. The map packingGridEquiv removes positions "
                + "0 and 3j+1 and subtracts one from each remaining rank. Its inverse "
                + "adds one to every grid rank and inserts the forced ranks 0 and "
                + "3j+1. The column and horizontal inequalities recover all four "
                + "comparisons of every window, including the first and last windows. "
                + "The two maps are inverse on actual permutations, so no labeling "
                + "or symmetry factor occurs."),
            Paragraph(Text("A first-z insertion/deletion bijection is still required "
                + "to identify this grid cardinality with the transfer rows. Neither "
                + "modular conclusion for the actual count follows from the "
                + "endpoint-deletion equality alone.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("bks14325-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Call(string f, params Formula[] a) => new Formula.Apply(F.Id(f), [.. a]);
    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Length => Add(D(5), Mul(Sub(F.Id("j"), D(1)), D(3)));
    private static Formula Last => Add(Mul(D(3), F.Id("j")), D(1));
    private static Formula Finite => Call("Fin", Length);
    private static Formula W(Formula x) => Call("w", x);
    private static Formula All(string v, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(v), Colon, Sp, type, Comma, Sp, body);
    private static Formula Imply(Formula a, Formula b) => Seq(Open, a, Close, Sp, Implies, Sp, b);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Both(Formula a, Formula b) => Seq(Open, a, Close, Sp, Land, Sp, Open, b, Close);
    private static Formula Guarded(Formula wType, Formula conclusion) =>
        All("j", Natural, Imply(Seq(D(1), Sp, Leq, Sp, F.Id("j")), All("w", wType,
            Imply(Call("Packs", F.Id("pattern"), D(2), F.Id("j"), F.Id("w")), conclusion))));
    private static Formula BoundsFormula() => Disp(Guarded(new Formula.TypeArrow(Finite, Finite),
        All("x", Finite, Both(Seq(W(D(0)), Sp, Leq, Sp, W(F.Id("x"))),
            Seq(W(F.Id("x")), Sp, Leq, Sp, W(Last))))));
    private static Formula ExtremaFormula() => Disp(Guarded(Call("Perm", Finite),
        Both(Equal(W(D(0)), D(0)), Equal(W(Last), Last))));
    private static Formula CountFormula() => Disp(All("j", Natural,
        Imply(Seq(D(1), Sp, Leq, Sp, F.Id("j")),
            Equal(Call("count", F.Id("pattern"), D(2), F.Id("j")),
                Call("card", Call("GridPacking", F.Id("j")))))));
}
