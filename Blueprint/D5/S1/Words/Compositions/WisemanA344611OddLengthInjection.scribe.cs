using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class WisemanA344611OddLengthInjectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/WisemanA344611OddLengthInjection.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/PermutationPatterns/oeis2021a344611");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative reverse-alternating partitions inject into odd-length partitions of the next weight.",
        H("Wiseman A344611: odd-length partition injection"),
        Blocks(
            Node("reverseAlternatingSum", "Reverse-alternating sum", ReverseSumFormula(),
                "OEIS A344611 revision 27, COMMENTS (electronic entry, no page number): "
                + "“The reverse-alternating sum of a partition (y_1,...,y_k) is Sum_i (-1)^(k-i) y_i.” "
                + "The parts are sorted decreasingly by Multiset.sort. The integer recurrence starts at zero and replaces z by a-z for each part a. "
                + "Its last endpoint is this sum; List.getLastD gives zero for the empty list.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a344611", "The A344611 count", CountFormula("a344611", SourceCount()),
                "OEIS A344611 revision 27, NAME (electronic entry, no page number): "
                + "“Number of integer partitions of 2*n with reverse-alternating sum >= 0.” "
                + "Nat.card counts the finite subtype with that integer inequality.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a160786", "The odd-length target count", CountFormula("a160786", TargetCount()),
                "OEIS A160786 revision 25, FORMULA: “a(n) = A027193(2n+1).” "
                + "OEIS A027193 revision 78, NAME: “Number of partitions of n into an odd number of parts.” "
                + "These electronic entries have no page numbers. Odd refers to the number of parts, "
                + "represented by p.parts.card, with no restriction on the sizes of individual parts.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The source comparison", Disp(Seq(V("claim"), Sp, Iff, Sp,
                    Parenthesized(ClaimBody()))),
                "OEIS A344611 revision 27, FORMULA (electronic entry, no page number): "
                + "“Conjecture: a(n) <= A160786(n). The difference is 0, 0, 0, 0, 1, 2, 4, 9, 16, 28, 48, 79, ...” "
                + "The quantifier includes zero: OFFSET is “0,2”, and the source example includes ().",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The partition-count inequality", Disp(ClaimBody()),
                "Increase the first part of an odd-length source by one, and append 1 to an even-length source. "
                + "Both operations preserve decreasing order and positivity, increase the weight by one, "
                + "and give odd length. A two-step integer endpoint bound forces the first two parts "
                + "of a nonempty even-length source with nonnegative sum to agree. Thus the odd branch "
                + "has a unique largest part and the even branch has a repeated largest part. "
                + "The empty source maps to [1]. Inverting each branch gives an injection for every "
                + "source weight m into odd-length partitions of m+1; cardinal comparison at m=2*n proves the inequality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wiseman-a344611"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a344611-" + name.ToLowerInvariant()),
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
    private static Formula All(string variable, Formula type, Formula body) => Seq(
        Forall, Sp, Parenthesized(Seq(V(variable), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Partition(Formula weight) => App(Qualified("Nat", "Partition"), weight);
    private static Formula Parts() => Seq(V("p"), Dot, V("parts"));
    private static Formula SortedParts() => App(Qualified("Multiset", "sort"), Parts(),
        Parenthesized(Seq(Parenthesized(Seq(V("a"), Sp, V("b"), Colon, Sp, Nat())),
            Sp, Mapsto, Sp, V("a"), Sp, Ge, Sp, V("b"))));
    private static Formula ReverseSumFormula() => Disp(All("m", Nat(),
        All("p", Partition(V("m")), Seq(Call("reverseAlternatingSum", V("p")), Sp, Eq, Sp,
            App(Qualified("List", "getLastD"),
                App(Qualified("TrimmedAlternatingPartitions", "trimmedSums"), SortedParts()),
                D(0))))));
    private static Formula Subtype(Formula weight, Formula predicate) => Call("Subtype",
        Parenthesized(Seq(Parenthesized(Seq(V("p"), Colon, Sp, Partition(weight))),
            Sp, Mapsto, Sp, predicate)));
    private static Formula SourceCount() => App(Qualified("Nat", "card"),
        Subtype(Seq(D(2), Sp, Cdot, Sp, V("n")), Seq(D(0), Sp, Le, Sp, Call("reverseAlternatingSum", V("p")))));
    private static Formula TargetCount() => App(Qualified("Nat", "card"),
        Subtype(Seq(D(2), Sp, Cdot, Sp, V("n"), Plus, D(1)),
            Call("Odd", Seq(Parts(), Dot, V("card")))));
    private static Formula CountFormula(string name, Formula count) => Disp(All("n", Nat(),
        Seq(Call(name, V("n")), Sp, Eq, Sp, count)));
    private static Formula ClaimBody() => All("n", Nat(), Seq(
        Call("a344611", V("n")), Sp, Le, Sp, Call("a160786", V("n"))));
}
