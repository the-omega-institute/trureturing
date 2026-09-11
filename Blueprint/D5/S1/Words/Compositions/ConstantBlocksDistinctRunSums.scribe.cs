using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class ConstantBlocksDistinctRunSumsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/ConstantBlocksDistinctRunSums.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/oeis2026a382427");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct-sum constant blocks exist exactly when an ordering has distinct maximal run sums.",
        H("Constant Blocks and Distinct Run Sums"),
        Blocks(
            Paragraph(Text("OEIS A382427 compares two existence predicates on positive integer "
                + "partitions. A block is encoded as (value, multiplicity), with both entries "
                + "positive. Blocks may share a value, but their sums must all differ. "
                + "A381717 states the pointwise equivalence for the complementary class.")),
            Node("HasConstantBlocks", "Constant blocks with distinct sums", BlocksFormula(),
                "The finite set records every block. A repeated identical block would repeat "
                + "its sum, so no valid decomposition is lost by using a set. Replicate(c,v) "
                + "is the multiset containing c copies of v; the multiset sum preserves every "
                + "part and its multiplicity. InjOn requires distinct sums across all values.",
                DescribeRole.Definition),
            Node("runSums", "Maximal constant runs", RunsFormula(),
                "Mathlib List.splitBy with Boolean equality splits at each change of value. "
                + "The resulting runs are maximal; mapping List.sum takes their sums. "
                + "The empty list has no runs and no sums.", DescribeRole.Definition),
            Node("HasDistinctRunSums", "An ordering with distinct run sums", OrderingFormula(),
                "Equality of the underlying multiset expresses that the list is a permutation "
                + "of the parts. Nodup tests all run sums together. No ordering of the parts "
                + "is fixed in advance, and only existence is counted.", DescribeRole.Definition),
            Node("constantBlocks_iff_distinctRunSums", "Pointwise equivalence", MainFormula(),
                "Choose a valid decomposition with the fewest blocks. If k blocks share a "
                + "value and there are o other blocks, k > o+1 supplies k-1 different candidate "
                + "sums by adding the largest same-value sum to each remaining one. Each "
                + "candidate exceeds every old same-value sum, so one avoids all o other sums. "
                + "Merging that pair contradicts minimality. Thus every color count obeys "
                + "2k <= total+1. A greedy induction, retaining a forbidden first color, "
                + "orders the blocks with adjacent values different. Mathlib splitBy_flatten "
                + "then certifies that these blocks are exactly the maximal runs. Conversely, "
                + "the maximal runs themselves provide the constant-block decomposition.",
                DescribeRole.Theorem),
            Node("card_constantBlocks_eq_distinctRunSums", "The A382427 counting identity", CountFormula(),
                "The pointwise equivalence identifies two filters of the same finite type "
                + "Nat.Partition(n), and hence their cardinalities. This holds for every n, "
                + "including n=0, whose unique partition is empty and satisfies both predicates.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a382427-constant-blocks-distinct-run-sums"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a382427-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Lambda(string name, Formula body) =>
        Par(Seq(V(name), Sp, Mapsto, Sp, body));
    private static Formula Lists() => Call("List", Nat());
    private static Formula Multisets() => Call("Multiset", Nat());
    private static Formula BlockSets() => Call("Finset", Par(Seq(Nat(), Times, Nat())));
    private static Formula Weight() => Lambda("b", Seq(Call("fst", V("b")), Sp,
        Cdot, Sp, Call("snd", V("b"))));
    private static Formula Parts() => Lambda("b",
        Call("replicate", Call("snd", V("b")), Call("fst", V("b"))));
    private static Formula PositiveBlocks() => Par(Seq(Forall, Sp, V("b"), Sp, InMacro, Sp,
        V("s"), Comma, Sp, D(0), Lt, Call("fst", V("b")), Sp, Land, Sp,
        D(0), Lt, Call("snd", V("b"))));
    private static Formula BlocksFormula() => Disp(All(V("m"), Multisets(), Seq(
        Call("HasConstantBlocks", V("m")), Sp, Iff, Sp,
        Par(Seq(Exists, Sp, V("s"), Colon, Sp, BlockSets(), Comma, Sp,
            PositiveBlocks(), Sp, Land, Sp, Call("InjOn", Weight(), V("s")), Sp, Land, Sp,
            Call("sum", V("s"), Parts()), Sp, Eq, Sp, V("m"))))));
    private static Formula RunsFormula() => Disp(All(V("l"), Lists(), Seq(
        Call("runSums", V("l")), Sp, Eq, Sp, Call("map", V("sum"),
            Call("splitBy", Par(Seq(V("a"), Comma, V("b"), Sp, Mapsto, Sp,
                Call("beq", V("a"), V("b")))), V("l"))))));
    private static Formula OrderingFormula() => Disp(All(V("m"), Multisets(), Seq(
        Call("HasDistinctRunSums", V("m")), Sp, Iff, Sp,
        Par(Seq(Exists, Sp, V("l"), Colon, Sp, Lists(), Comma, Sp,
            Par(Seq(V("l"), Colon, Sp, Multisets())), Sp, Eq, Sp, V("m"), Sp, Land, Sp,
            Call("Nodup", Call("runSums", V("l"))))))));
    private static Formula MainFormula() => Disp(All(V("n"), Nat(),
        All(V("p"), Call("Partition", V("n")), Seq(
            Call("HasConstantBlocks", Call("parts", V("p"))), Sp, Iff, Sp,
            Call("HasDistinctRunSums", Call("parts", V("p")))))));
    private static Formula Count(string predicate) => Call("card", Call("filter",
        Lambda("p", Call(predicate, Call("parts", V("p")))),
        Par(Seq(Call("univ"), Colon, Sp, Call("Finset", Call("Partition", V("n")))))));
    private static Formula CountFormula() => Disp(All(V("n"), Nat(), Seq(
        Count("HasConstantBlocks"), Sp, Eq, Sp, Count("HasDistinctRunSums"))));
}
