using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class ChoosableInitialIntervalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/ChoosableInitialIntervals.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/oeis2026a388711");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct representatives of increasing initial intervals exist exactly above the diagonal.",
        H("Choosable Initial Intervals"),
        Blocks(
            Paragraph(Text("OEIS A388711 compares partitions with choosable initial intervals "
                + "and superdiagonal reversed partitions. Ordinary parts are sorted decreasingly; "
                + "reversed parts are sorted increasingly. Indices below start at zero, "
                + "so the diagonal condition contains i+1. All parts and representatives are naturals.")),
            Node("ChoosableInitial", "Distinct positive representatives", ChoosableFormula(),
                "A representative is chosen at each list position, is at least one, "
                + "and is at most that position's part. Injectivity makes the choices distinct. "
                + "A zero part has no allowed choice; the empty family is choosable.",
                DescribeRole.Definition),
            Node("Superdiagonal", "The diagonal condition", DiagonalFormula(),
                "The part at zero-based position i is at least i+1. The list theorem "
                + "does not assume positivity; the condition itself implies it.",
                DescribeRole.Definition),
            Node("choosableInitial_congr_perm", "Order invariance", PermutationFormula(),
                "Represent the choice map as a nodup list related positionwise to the parts. "
                + "Mathlib's relational permutation lemma transports that list and preserves "
                + "nodup. Thus choosability depends only on the multiset of parts.",
                DescribeRole.Lemma),
            Node("choosableInitial_iff_superdiagonal", "The initial-interval criterion", MainFormula(),
                "Restrict the injection to the first i+1 positions. Monotonicity bounds all "
                + "these positive representatives by the part at i. Subtracting one gives an "
                + "injection Fin(i+1) into Fin(l[i]); finite cardinal comparison proves the bound. "
                + "In the other direction choose i+1. This elementary criterion is not claimed "
                + "as a new mathematical theorem or a new form of Hall's theorem.",
                DescribeRole.Theorem),
            Node("card_choosable_eq_superdiagonal", "Equality of the two partition counts", CountFormula(),
                "Both filters range over Mathlib's partitions of n and require exactly k "
                + "positive parts. Order invariance relates descending and ascending order; "
                + "the initial-interval criterion then identifies the predicates. The equality "
                + "holds for all n and k, including the empty partition at n=k=0.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a388711-choosable-initial-intervals"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a388711-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Len(Formula l) => Call("length", l);
    private static Formula Indices(Formula l) => Call("Fin", Len(l));
    private static Formula Get(Formula l, Formula i) => Call("get", l, i);
    private static Formula Choose(Formula l) => Call("ChoosableInitial", l);
    private static Formula Diagonal(Formula l) => Call("Superdiagonal", l);
    private static Formula Lists() => Call("List", Nat());
    private static Formula Bounds() => Seq(D(1), Sp, Le, Sp, Call("f", V("i")), Sp,
        Land, Sp, Call("f", V("i")), Sp, Le, Sp, Get(V("l"), V("i")));
    private static Formula ChoosableFormula() => Disp(All(V("l"), Lists(), Seq(
        Choose(V("l")), Sp, Iff, Sp, Par(Seq(Exists, Sp, V("f"), Colon, Sp,
            Indices(V("l")), Sp, Rightarrow, Sp, Nat(), Comma, Sp,
            Call("Injective", V("f")), Sp, Land, Sp,
            Par(All(V("i"), Indices(V("l")), Bounds())))))));
    private static Formula DiagonalFormula() => Disp(All(V("l"), Lists(), Seq(
        Diagonal(V("l")), Sp, Iff, Sp, Par(All(V("i"), Indices(V("l")), Seq(
            V("i"), Sp, Plus, Sp, D(1), Sp, Le, Sp, Get(V("l"), V("i"))))))));
    private static Formula Relation(Formula op) => Par(Seq(V("a"), Comma, Sp, V("b"),
        Sp, Mapsto, Sp, V("a"), Sp, op, Sp, V("b")));
    private static Formula MainFormula() => Disp(All(V("l"), Lists(), Seq(
        Call("Pairwise", Relation(Le), V("l")), Sp, Implies, Sp,
        Par(Seq(Choose(V("l")), Sp, Iff, Sp, Diagonal(V("l")))))));
    private static Formula PermutationFormula() => Disp(All(V("l"), Lists(),
        All(V("m"), Lists(), Seq(Call("Perm", V("l"), V("m")), Sp, Implies, Sp,
            Par(Seq(Choose(V("l")), Sp, Iff, Sp, Choose(V("m"))))))));
    private static Formula Count(Formula predicate, Formula order) => Call("card", Call("filter",
        Par(Seq(V("p"), Sp, Mapsto, Sp, Call("card", Call("parts", V("p"))), Sp,
            Eq, Sp, V("k"), Sp, Land, Sp,
            new Formula.Apply(predicate, [Call("sort", Call("parts", V("p")), Relation(order))]))),
        Par(Seq(Call("univ"), Colon, Sp, Call("Finset", Call("Partition", V("n")))))));
    private static Formula CountFormula() => Disp(All(V("n"), Nat(), All(V("k"), Nat(), Seq(
        Count(V("ChoosableInitial"), Ge), Sp, Eq, Sp, Count(V("Superdiagonal"), Le)))));
}
