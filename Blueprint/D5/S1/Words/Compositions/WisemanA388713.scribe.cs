using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class WisemanA388713Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/WisemanA388713.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/oeis2025wisemanpartitions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The partition predicates give equal counts with a fixed maximum.", H("Wiseman A388713"), Blocks(
            Node("T", "Superdiagonal reversed partitions by maximum", DefinitionFormula("T", FirstPredicate()),
                "OEIS A388713 counts superdiagonal multisets summing to n with maximum k. Ascending parts represent reversed partitions, the weak diagonal bound uses index plus one, and Multiset.sup supplies the maximum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("choosable", "Choosable partitions by maximum", DefinitionFormula("choosable", SecondPredicate()),
                "The conjectured count in OEIS A388713 uses partitions of n with maximum k and choosable initial intervals. The empty partition has maximum zero and satisfies both predicates, so both formal counts are 1 at (0,0); the printed source row is 0.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjectured maximum-refined equality", Disp(Seq(V("claim"), Sp, Iff, Sp,
                    Parenthesized(ClaimBody()))),
                "For every pair of natural numbers n and k, the superdiagonal reversed-partition count equals the choosable partition count with the same maximum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Equality of the partition counts by maximum", Disp(ClaimBody()),
                "WisemanA388712.sorted_choosable_iff_superdiagonal identifies the two predicates. Its reverse direction and the common maximum-part condition give identical filters, whose cardinalities agree.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wiseman-a388713"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a388713-" + name.Replace('_', '-').Replace('.', '-').ToLowerInvariant()),
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
    private static Formula FirstPredicate() => Seq(App(Qualified("Multiset", "sup"), Parts()), Sp, Eq, Sp, V("k"), Sp, Land, Sp,
        Call("Superdiagonal", Sort(Parts(), Le)));
    private static Formula SecondPredicate() => Seq(App(Qualified("Multiset", "sup"), Parts()), Sp, Eq, Sp, V("k"), Sp, Land, Sp,
        Call("ChoosableInitial", Sort(Parts(), Ge)));
    private static Formula ClaimBody() => Quantify(Seq(
        Call("T", V("n"), V("k")), Sp, Eq, Sp, Call("choosable", V("n"), V("k"))));
}
