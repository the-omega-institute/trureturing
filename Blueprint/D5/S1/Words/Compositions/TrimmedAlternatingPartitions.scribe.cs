using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class TrimmedAlternatingPartitionsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/TrimmedAlternatingPartitions.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/oeis2026a392698");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Distinct trimmed alternating sums characterize strict partition tails and count strict partitions of n+1.",
        H("Trimmed Alternating Sums of Partitions"),
        Blocks(
            Paragraph(Text("Ordinary partitions are listed in weakly decreasing order. "
                + "Their trimmed alternating sums exclude the initial zero and use integer "
                + "subtraction. The corrected OEIS A392698 count has a shift by one; "
                + "distincts denotes Mathlib's Nat.Partition.distincts. "
                + "The unshifted source sentence is not the theorem proved here.")),
            Node("sumsFrom", "Integer recurrence", RecurrenceFormula(),
                "The initial accumulator z is excluded. A natural part a gives the next "
                + "integer value a-z; recursion continues from that value. In particular, "
                + "negative values are retained, rather than truncated by natural subtraction.",
                DescribeRole.Definition),
            Node("trimmedSums", "Trimmed sums", TrimmedFormula(),
                "Start the recurrence at zero. The output for the empty list is empty; "
                + "the output for [1,1] is [1,0], whose entries are distinct.",
                DescribeRole.Definition),
            Node("trimmedSums_nodup_iff_strict_tail", "The strict-tail criterion", MainFormula(),
                "For any positive decreasing list, distinctness is equivalent to strict "
                + "decrease of its tail. A two-step integer range induction separates the "
                + "signs and bounds later sums. Equal adjacent tail parts would repeat a sum "
                + "two positions later. The first two parts may be equal: [2,2,1] qualifies.",
                DescribeRole.Theorem),
            Node("card_trimmedSums_eq_distincts", "The corrected partition count", CountFormula(),
                "Increase the largest part by one, sending the empty partition to [1]. "
                + "The strict-tail criterion makes the image a distinct-part partition. "
                + "The inverse sends [1] to the empty partition and otherwise decreases "
                + "the maximum by one. Both maps preserve positivity and have the stated "
                + "weight change; their inverse laws give equality of the two cardinalities "
                + "for every n, including n=0, where both counts are one.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a392698-trimmed-alternating-partitions"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a392698-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Integer() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Lists() => Call("List", Nat());
    private static Formula Cons(Formula a, Formula q) => Call("cons", a, q);
    private static Formula Relation(Formula op) => Par(Seq(V("a"), Comma, Sp, V("b"),
        Sp, Mapsto, Sp, V("a"), Sp, op, Sp, V("b")));
    private static Formula RecurrenceFormula() => Disp(All(V("z"), Integer(), Seq(
        Call("sumsFrom", V("z"), Call("nil")), Sp, Eq, Sp, Call("nil"), Sp, Land, Sp,
        Par(All(V("a"), Nat(), All(V("q"), Lists(), Seq(
            Call("sumsFrom", V("z"), Cons(V("a"), V("q"))), Sp, Eq, Sp,
            Cons(Seq(V("a"), Minus, V("z")),
                Call("sumsFrom", Seq(V("a"), Minus, V("z")), V("q"))))))))));
    private static Formula TrimmedFormula() => Disp(All(V("q"), Lists(), Seq(
        Call("trimmedSums", V("q")), Sp, Eq, Sp, Call("sumsFrom", D(0), V("q")))));
    private static Formula Positive() => Par(All(V("a"), Nat(), Seq(
        V("a"), Sp, InMacro, Sp, V("q"), Sp, Implies, Sp, D(0), Sp, Lt, Sp, V("a"))));
    private static Formula MainFormula() => Disp(All(V("q"), Lists(), Seq(
        Par(Seq(Call("Pairwise", Relation(Ge), V("q")), Sp, Land, Sp, Positive())),
        Sp, Implies, Sp, Par(Seq(Call("Nodup", Call("trimmedSums", V("q"))), Sp,
            Iff, Sp, Call("Pairwise", Relation(Gt), Call("tail", V("q"))))))));
    private static Formula CountFormula() => Disp(All(V("n"), Nat(), Seq(
        Call("card", Call("filter", Par(Seq(V("p"), Sp, Mapsto, Sp,
            Call("Nodup", Call("trimmedSums", Call("sort", Call("parts", V("p")),
                Relation(Ge)))))), Par(Seq(Call("univ"), Colon, Sp,
                    Call("Finset", Call("Partition", V("n"))))))), Sp, Eq, Sp,
        Call("card", Call("distincts", Seq(V("n"), Plus, D(1)))))));
}
