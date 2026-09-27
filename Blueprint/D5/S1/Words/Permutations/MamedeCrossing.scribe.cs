using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeCrossingDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/MamedeCrossing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduced crossings constrain guarded strand traces.",
        H("Guarded Pair Crossings"),
        Blocks(
            Paragraph(Text("In a reduced adjacent-swap word the same pair of values cannot "
                + "cross twice. A final-order guard consequently prevents the tracked value "
                + "from stepping right.")),
            Node("guarded_walk_endpoint", "Guarded strand endpoint", Disp(Q(
                Call("Bounds", V("n"), V("i"), V("t")), Land,
                V("i"), Le, Call("oneBased", V("x")), Land,
                Call("position", V("n"), V("t")), Eq, V("x"), Land,
                Call("Reduced", V("n"), V("b")), Land,
                Call("prod", V("n"), V("b")),
                Call("position", V("n"), V("i")), Eq, V("x"), Land,
                Call("FinalPrefixGuard", V("n"), V("i"), V("x"), V("b")),
                Implies, Call("leftOnly", V("t"), V("b")), Land,
                Call("traceEnd", V("t"), V("b")), Eq, V("i"))),
                "Bounds means 1<=i,t<=n+1, and oneBased(x)=x.val+1. "
                    + "FinalPrefixGuard requires every initial position r with r+1<i "
                    + "to finish strictly below x. The conclusion holds for the actual "
                    + "reduced word b, without assuming a decomposition of b.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("mamede-crossing-" + name.Replace('_', '-').ToLowerInvariant()),
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
