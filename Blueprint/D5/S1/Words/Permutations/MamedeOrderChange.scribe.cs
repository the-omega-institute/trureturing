using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeOrderChangeDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/MamedeOrderChange.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A change in the order of two values has a crossing generator.",
        H("Order Change and Pair Crossing"),
        Blocks(
            Paragraph(Text("Relative order is measured by the inverse permutation, so "
                + "it compares the positions occupied by two values rather than their values.")),
            Node("before", "Relative order", Disp(Q(
                Call("before", V("sigma"), V("x"), V("y")), Iff,
                Call("positionOf", V("sigma"), V("x")), Lt,
                Call("positionOf", V("sigma"), V("y")))),
                "The inverse image of x has smaller Fin value than the inverse image of y.",
                DescribeRole.Definition),
            Node("crossing", "Pair crossing", Disp(Q(
                Call("crossing", V("sigma"), V("k"), V("x"), V("y")), Iff,
                Call("occupyAdjacent", V("sigma"), V("k"), V("x"), V("y")),
                Lor, Call("occupyAdjacent", V("sigma"), V("k"), V("y"), V("x")))),
                "The values x and y occupy the two positions swapped by generator k, "
                    + "in either order.", DescribeRole.Definition),
            Node("order_change_has_crossing", "A reversal has a crossing", Disp(Q(
                Call("Valid", V("n"), V("w")), Land, V("x"), Neq, V("y"),
                Land, Call("before", V("sigma"), V("x"), V("y")), Neq,
                Call("before", Q(V("sigma"), Times, Call("prod", V("n"), V("w"))),
                    V("x"), V("y")),
                Implies, Exists, V("p"), Comma, Exists, V("k"), Comma,
                Exists, V("q"), Comma,
                V("w"), Eq, Call("concat", V("p"), V("k"), V("q")),
                Land, Call("crossing", Q(V("sigma"), Times, Call("prod", V("n"), V("p"))),
                    V("k"), V("x"), V("y")))),
                "For every valid adjacent-swap word, a change in pair order occurs at "
                    + "an actual letter of that word and its preceding prefix product.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("mamede-order-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Root + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

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

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
}
