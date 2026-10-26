using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class WisemanA387118Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/WisemanA387118.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/oeis2025wisemanpartitions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complemented partition predicates give equal totals.", H("Wiseman A387118"), Blocks(
            Node("a", "Partitions without choosable initial intervals", DefinitionFormula("a", FirstPredicate()),
                "OEIS A387118 counts integer partitions of n without choosable initial intervals. The filter ranges over Nat.Partition n, whose parts are positive, and descending order represents ordinary partitions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("nonSuperdiagonal", "Nonsuperdiagonal reversed partitions", DefinitionFormula("nonSuperdiagonal", SecondPredicate()),
                "The conjectured count in OEIS A387118 uses reversed partitions, represented by ascending parts, that fail the one-based weak diagonal bound.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured total equality", Disp(Seq(V("claim"), Sp, Iff, Sp,
                    Parenthesized(ClaimBody()))),
                "The two counts are equal for every natural number n, without fixing a further partition statistic.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Equality of the total partition counts", Disp(ClaimBody()),
                "WisemanA388712.sorted_choosable_iff_superdiagonal identifies choosability of descending parts with superdiagonality of ascending parts. Negation gives equal filters on the same finite set of partitions and hence equal cardinalities.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wiseman-a387118"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a387118-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
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
    private static Formula Quantify(Formula body) => All(V("n"), Nat(), body);
    private static Formula DefinitionFormula(string name, Formula predicate) => Disp(Quantify(Seq(
        Call(name, V("n")), Sp, Eq, Sp, Count(predicate))));
    private static Formula FirstPredicate() =>
        new Formula.Not(Call("ChoosableInitial", Sort(Parts(), Ge)));
    private static Formula SecondPredicate() =>
        new Formula.Not(Call("Superdiagonal", Sort(Parts(), Le)));
    private static Formula ClaimBody() => Quantify(Seq(
        Call("a", V("n")), Sp, Eq, Sp, Call("nonSuperdiagonal", V("n"))));
}
