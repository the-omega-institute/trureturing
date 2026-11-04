using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class WisemanA388712Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/WisemanA388712.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/oeis2025wisemanpartitions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two partition predicates give equal counts.", H("Wiseman A388712"), Blocks(
            Node("T", "Partitions without choosable initial intervals", DefinitionFormula("T", FirstPredicate()),
                "Triangle read by rows where T(n,k) is the number of integer partitions of n into k parts without choosable initial intervals. OEIS A388712, Name (unpaginated). The counts range over Nat.Partition n, whose parts are positive. Descending order represents ordinary partitions; ascending order represents reversed partitions. List indices start at zero, so Superdiagonal uses i+1.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("nonSuperdiagonal", "Nonsuperdiagonal reversed partitions", DefinitionFormula("nonSuperdiagonal", SecondPredicate()),
                "Conjecture: Also the number of non-superdiagonal reversed partitions of n into k parts, where a sequence (y_1, ..., y_k) is superdiagonal iff y_i >= i for all i = 1..k. OEIS A388712, Comments (unpaginated). The counts range over Nat.Partition n, whose parts are positive. Descending order represents ordinary partitions; ascending order represents reversed partitions. List indices start at zero, so Superdiagonal uses i+1.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured equality", Disp(Seq(V("claim"), Sp, Iff, Sp,
                    Parenthesized(ClaimBody()))),
                "Conjecture: Also the number of non-superdiagonal reversed partitions of n into k parts, where a sequence (y_1, ..., y_k) is superdiagonal iff y_i >= i for all i = 1..k. OEIS A388712, Comments (unpaginated). The equality quantifies over every pair of naturals n and k.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("sorted_choosable_iff_superdiagonal", "The two sort orders",
                Disp(All(V("s"), Call("Multiset", Nat()), Seq(
                    Call("ChoosableInitial", Sort(V("s"), Ge)), Sp, Iff, Sp,
                    Call("Superdiagonal", Sort(V("s"), Le))))),
                "For every multiset of naturals, choosability of the descending list is "
                    + "equivalent to superdiagonality of the ascending list. Permutation invariance "
                    + "and the increasing-list criterion prove the equivalence, including the empty "
                    + "multiset and multisets containing zeros. All three partition identities use it.",
                DescribeRole.Lemma, AssessedProvenance.FromRepo()),
            Node("result", "Equality of the partition counts", Disp(ClaimBody()),
                "The two filters have the same truth value on each partition, so their "
                    + "finite cardinalities agree. The sorted-list equivalence identifies the "
                    + "predicates under negation and preserves the number of parts.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wiseman388-partitions"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a388712-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(V(owner)), Dot, Operatorname, Grp(V(name)));
    private static Formula App(Formula function, params Formula[] args) =>
        new Formula.Apply(function, [.. args]);
    private static Formula Call(string name, params Formula[] args) =>
        App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Parts() => Seq(V("p"), Dot, V("parts"));
    private static Formula Relation(Formula order) => Parenthesized(Seq(
        Parenthesized(Seq(V("a"), Sp, V("b"), Colon, Sp, Nat())), Sp, Mapsto, Sp,
        V("a"), Sp, order, Sp, V("b")));
    private static Formula Sort(Formula parts, Formula order) =>
        App(Qualified("Multiset", "sort"), parts, Relation(order));
    private static Formula PartitionType() => App(Qualified("Nat", "Partition"), V("n"));
    private static Formula Count(Formula predicate) => App(Qualified("Finset", "card"),
        App(Qualified("Finset", "filter"), Parenthesized(Seq(
            Parenthesized(Seq(V("p"), Colon, Sp, PartitionType())), Sp, Mapsto, Sp, predicate)),
            Parenthesized(Seq(Qualified("Finset", "univ"), Colon, Sp,
                Call("Finset", PartitionType())))));
    private static Formula Quantify(Formula body) => All(V("n"), Nat(), All(V("k"), Nat(), body));
    private static Formula DefinitionFormula(string name, Formula predicate) => Disp(Quantify(Seq(
        Call(name, V("n"), V("k")), Sp, Eq, Sp, Count(predicate))));
    private static Formula FirstPredicate() => Seq(App(Qualified("Multiset", "card"), Parts()), Sp, Eq, Sp, V("k"), Sp, Land, Sp,
        new Formula.Not(Call("ChoosableInitial", Sort(Parts(), Ge))));
    private static Formula SecondPredicate() => Seq(App(Qualified("Multiset", "card"), Parts()), Sp, Eq, Sp, V("k"), Sp, Land, Sp,
        new Formula.Not(Call("Superdiagonal", Sort(Parts(), Le))));
    private static Formula ClaimBody() => Quantify(Seq(
        Call("T", V("n"), V("k")), Sp, Eq, Sp, Call("nonSuperdiagonal", V("n"), V("k"))));
}
