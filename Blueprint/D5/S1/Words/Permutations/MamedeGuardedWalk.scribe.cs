using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeGuardedWalkDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/MamedeGuardedWalk.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A one-sided strand trace forces a complete descending run.",
        H("Guarded Walk Factorization"),
        Blocks(
            Paragraph(Text("A strand at one-based position t can move left across generator "
                + "k when k+1=t. The guard rules out a rightward move across k=t.")),
            Node("leftStep", "Left step", Disp(Q(Call("leftStep", V("t"), V("k")), Eq,
                Call("ifEq", Q(V("k"), Plus, D(1)), V("t"), V("k"), V("t")))),
                "The position drops to k exactly when k+1=t.", DescribeRole.Definition),
            Node("traceEnd", "Trace endpoint", Disp(Q(
                Call("traceEnd", V("t"), V("w")), Eq,
                Call("foldLeftSteps", V("t"), V("w")))),
                "The endpoint applies leftStep in list order.", DescribeRole.Definition),
            Node("leftOnly", "No right step", Disp(Q(
                Call("leftOnly", V("t"), V("w")), Iff,
                Call("everyStepAvoidsCurrentGenerator", V("t"), V("w")))),
                "Each next generator differs from the current trace position.",
                DescribeRole.Definition),
            Node("traceEnd_le", "Trace monotonicity", Disp(Q(
                Forall, V("t"), Comma, Forall, V("w"), Comma,
                Call("traceEnd", V("t"), V("w")), Le, V("t"))),
                "Every trace step stays put or decreases the position.", DescribeRole.Theorem),
            Node("forced_descent", "Forced descending run", Disp(Q(
                V("i"), Le, V("j"), Land, Call("Consecutive", V("w")),
                Land, Call("leftOnly", Q(V("j"), Plus, D(1)), V("w")),
                Land, Call("traceEnd", Q(V("j"), Plus, D(1)), V("w")), Eq, V("i"),
                Implies, Exists, V("p"), Comma, Exists, V("q"), Comma,
                V("w"), Eq, Call("concat", V("p"), Call("desc", V("j"), V("i")), V("q")),
                Land, Call("PrefixBelow", V("p"), V("j")),
                Land, Call("SuffixAbove", V("q"), V("i")))),
                "Every prefix letter is less than j and every suffix letter is greater "
                    + "than i. The result is for arbitrary finite words and unbounded indices.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("mamede-walk-" + name.Replace('_', '-').ToLowerInvariant()),
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
