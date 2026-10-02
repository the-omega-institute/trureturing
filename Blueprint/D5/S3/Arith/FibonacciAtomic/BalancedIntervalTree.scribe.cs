using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class BalancedIntervalTreeDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordered interval bisection controls all node blocks and attains logarithmic height.",
        H("Balanced Interval Trees"),
        Blocks(
            Paragraph(Text("Coordinates are numbered from zero through k. For natural l and positive w "
                + "with l+w at most k+1, the block is the half-open interval from l to l+w. "
                + "Task leaves carry distinct coordinates. A fork has two nonempty children with "
                + "disjoint leaf blocks. Height counts edges, so a terminal has height zero.")),
            Describe.Lean(DescribeId.Create("balanced-interval-tree"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/BalancedIntervalTree.result"),
                H("Every Node of a Balanced Bisection"),
                StatementSource.FromAuthor(Seq(
                    D(0), Lt, V("w"), Sp, Land, Sp,
                    Add(V("l"), V("w")), Le, Add(V("k"), D(1)), Sp, Implies, Sp,
                    Exists, Sp, V("T"), Comma, Sp, Call("Full", V("T")), Sp, Land, Sp,
                    Call("leaves", V("T")), Eq, Call("interval", V("l"), Add(V("l"), V("w"))),
                    Sp, Land, Sp, Call("height", V("T")), Eq, Call("clog", D(2), V("w")),
                    Sp, Land, Sp, Forall, Sp, V("S"), InMacro, Call("subtrees", V("T")), Comma,
                    Sp, Exists, Sp, V("a"), Comma, V("b"), Comma, Sp,
                    V("l"), Le, V("a"), Lt, V("b"), Le, Add(V("l"), V("w")),
                    Sp, Land, Sp, Call("leaves", V("S")), Eq, Call("interval", V("a"), V("b")),
                    Sp, Land, Sp, Grp(Seq(V("a"), Eq, V("l"), Sp, Lor, Sp,
                        Seq(V("b"), Minus, V("a")), Le, Call("floorHalf", V("w")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every subtree has a nonempty adjacent coordinate block inside the "
                        + "original interval. If its left endpoint differs from l, its length is at most "
                        + "the integer floor of w/2. This includes every descendant, not only the root's "
                        + "two children.")),
                    Paragraph(Text("For length greater than one, divide into a leading block of length "
                        + "ceil(w/2) and a trailing block of length floor(w/2), then apply the same construction "
                        + "recursively. The child blocks partition the parent interval. The larger half "
                        + "determines the height through the ceiling-logarithm recurrence. A descendant "
                        + "of the trailing half stays inside that half; a nonleading descendant of the "
                        + "leading half is bounded by half the leading length."))), DescribeRole.Theorem))));
}
