using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Compositions;

internal sealed class PhiTailEncodingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Compositions/PhiTailEncoding.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Admissible A392714 permutations produce bounded reversed tail words.",
        H("A392714 Phi Tail Encoding"),
        Blocks(
            Paragraph(Text("The source permutation fixes the distinguished zero. Read the "
                + "remaining positions from right to left and subtract n from each value. "
                + "The resulting integer word has length 2n-1 and uses the residual alphabet "
                + "strictly between -n and n.")),
            Node("tailWord_length", "Tail length", Q(
                Call("length", Call("tailWord", V("n"), V("p"), V("hn"))), Eq,
                Call("twoMul", V("n")), Minus, D(1)),
                "The reversed tail is indexed by Fin (2*n-1), so ofFn gives exactly that length.",
                DescribeRole.Theorem),
            Node("tailWord_entry_bounds", "Residual alphabet bounds", Q(
                Minus, V("n"), Lt, Call("tailWord", V("n"), V("p"), V("hn")), Lt, V("n")),
                "Fixing zero and injectivity of a permutation exclude the lower endpoint; "
                + "the Fin range bound gives the upper endpoint.", DescribeRole.Theorem),
            Node("mem_phi_tailWord_bounds", "Bounds for Phi members", Q(
                Call("p", V("inphi")), Implies, Call("residualBounds", V("p"))),
                "Membership in the source finite set supplies the fixed-zero hypothesis, "
                + "so every tail letter satisfies the same residual bounds.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("phi-tail-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => F.Id(name);
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
