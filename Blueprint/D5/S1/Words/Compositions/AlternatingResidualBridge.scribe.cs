using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class AlternatingResidualBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/AlternatingResidualBridge.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/codex2026a392714bridge");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Blocked alternating words correspond to interlaced residual pairs.",
        H("Alternating Words and Residual Intervals"),
        Blocks(
            Paragraph(Text("Let a and b permute 1 through m, and write A and B for their "
                + "prefix sums, starting at zero. The Lean permutations use Fin m, with "
                + "one added to each value. The results include m=0. This chapter treats "
                + "explicitly alternating words; the passage from all Wronskian "
                + "contribution permutations to these words remains to be proved.")),
            Node("Good", "Nonnegative heights", Q(Call("Good", V("h"), V("w")), Iff,
                Forall, V("k"), Comma, D(0), Le, V("k"), Le, Call("length", V("w")),
                Implies, D(0), Le, V("h"), Plus, Call("sum", Call("take", V("k"), V("w")))),
                "Good requires every height, including the initial and final heights, "
                + "to be nonnegative.", DescribeRole.Definition),
            Node("Unswappable", "Blocked disjoint pairs", Q(
                Call("Unswappable", V("h"), Call("cons", V("x"), Call("cons", V("y"), V("w")))),
                Iff, Call("not", Par(Q(D(0), Le, V("h"), Plus, V("x"), Land,
                    D(0), Le, V("h"), Plus, V("y")))), Land,
                Call("Unswappable", Q(V("h"), Plus, V("x"), Plus, V("y")), V("w"))),
                "A complete pair is blocked when its two orders cannot both start "
                + "legally at the current height. Continue after the pair; an empty "
                + "list or a singleton has no complete pair and satisfies this condition.",
                DescribeRole.Definition),
            Node("alternating", "Expanding pairs", Q(
                Call("alternating", Call("cons", Par(Q(V("a"), Comma, V("b"))), V("l"))),
                Eq, Call("cons", V("a"), Call("cons", Q(Minus, V("b")), Call("alternating", V("l"))))),
                "The entries of each pair are natural numbers. Expand a pair to its "
                + "first entry and the negation of its second entry, both as integers. "
                + "The empty list expands to the singleton zero.", DescribeRole.Definition),
            Node("encode", "Encoding two permutations", Q(Call("encode", V("a"), V("b")),
                Eq, Par(Q(Sub("a", D(1)), Comma, Minus, Sub("b", D(1)), Comma,
                    Seq(Dot, Dot, Dot), Comma, Sub("a", V("m")), Comma, Minus, Sub("b", V("m")), Comma, D(0)))),
                "Read the displayed a and b entries in one-based notation. This is "
                + "the explicit alternating word ending in zero.", DescribeRole.Definition),
            Node("encode_rule_iff", "The interval characterization", Q(
                Rule(), Iff, Call("InResidual", V("a"), V("b"))),
                "Before block i the height is A at i-1 minus B at i-1. The reversed "
                + "order is illegal exactly when A at i-1 is less than B at i; the "
                + "block endpoint is nonnegative exactly when B at i is at most A "
                + "at i. Induction over the blocks proves both implications, including "
                + "the initial and final heights.", DescribeRole.Theorem),
            Node("encode_injective", "Recovering the two permutations", Q(
                Call("encode", V("a"), V("b")), Eq, Call("encode", V("c"), V("d")),
                Implies, V("a"), Eq, V("c"), Land, V("b"), Eq, V("d")),
                "Equality at alternating positions recovers the entries of a and b "
                + "separately. Equality of the finite lists therefore gives equality "
                + "of both permutations.", DescribeRole.Theorem),
            Node("encoded_product_sign_sum", "Summing the product signs", Q(
                Sum, Underscore, Grp(V("a")), Sum, Underscore, Grp(Q(V("b"), Colon, Rule())),
                Call("sign", V("a")), Call("sign", V("b")), Eq, D(1)),
                "The sums range over permutations of Fin m. Apply the interval "
                + "characterization, factor out sign(a), and use the residual identity. "
                + "Only a equal to the identity contributes. This formula uses the "
                + "product of the two signs; identifying it with the sign of an "
                + "ambient contribution permutation is a separate remaining step.", DescribeRole.Theorem))));

    private static Formula Rule() => Q(Call("Good", D(0), Call("encode", V("a"), V("b"))),
        Land, Call("Unswappable", D(0), Call("encode", V("a"), V("b"))));
    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("alternating-residual-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Q(Open, value, Close);
    private static Formula Sub(string name, Formula index) => Q(V(name), Underscore, Grp(index));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[items.Length * 2 - 1];
        for (var i = 0; i < items.Length; i++)
        {
            spaced[2 * i] = items[i];
            if (i + 1 < items.Length) spaced[2 * i + 1] = Sp;
        }
        return Seq(spaced);
    }
}
