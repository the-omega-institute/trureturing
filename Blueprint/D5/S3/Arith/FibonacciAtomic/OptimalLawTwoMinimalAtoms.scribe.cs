using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class OptimalLawTwoMinimalAtomsDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, x, Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Ex(Formula x, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, x, Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula And(params Formula[] fs) => Seq(Open,
        Seq(fs.SelectMany((f, i) => i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray()), Close);
    private static Formula Ty(string name) => Seq(Mathbb, Grp(F.Id(name)));

    public DocumentDefinition Create()
    {
        var m = F.Id("m");
        var p = F.Id("p");
        var i = F.Id("i");
        var j = F.Id("j");
        var indices = Call("Fin", m);
        var t = Call("inf", Call("range", p));
        var hypotheses = And(
            Seq(D(2), Sp, Le, Sp, m),
            All(i, indices, Seq(D(0), Sp, Lt, Sp, Call("p", i))),
            Equal(Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, indices)), Call("p", i)), D(1)),
            Equal(Call("cost", p), Seq(Call("alpha", m), Sp, Cdot, Sp, t)));
        var conclusion = Ex(i, indices, Ex(j, indices,
            And(
                Seq(i, Sp, Neq, Sp, j),
                Equal(Call("p", i), t),
                Equal(Call("p", j), t))));
        var statement = All(m, Ty("N"), All(p, Seq(indices, Sp, To, Sp, Ty("R")),
            Imp(hypotheses, conclusion)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every positive attaining law has at least two labels at its minimum mass.",
            H("Two Minimum Atoms in Every Optimal Law"), Blocks(
                Describe.Lean(DescribeId.Create("result"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawTwoMinimalAtoms.result"),
                    H("At least two labels attain the minimum"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("Let p be a strictly positive normalized real law on at least two labels. Its dyadic cost equals alpha(m) times the infimum of its finite range. The conclusion supplies two distinct labels i and j whose masses both equal that infimum.")),
                        Paragraph(Text("Assume a unique minimum label k. The termination theorem places every larger atom on a dyadic grid. A common denominator gives positive integer numerators summing to a power of two; the least common denominator has positive depth, and the odd numerators form a nonempty even-cardinality set.")),
                        Paragraph(Text("If the minimum numerator is odd, any other odd numerator is at least two larger, so moving one deepest dyadic leaf from that atom to the minimum raises the minimum mass while preserving the dyadic grid. If the minimum numerator is even and an odd numerator is at least three larger, the same one-leaf transfer applies.")),
                        Paragraph(Text("In the remaining case there are two odd atoms with numerator exactly one above the even minimum. Moving one leaf from each to the minimum keeps the minimum mass fixed. All shallower floor counts weakly increase, with a strict increase at the preceding depth, while every deeper remainder is already zero. The resulting positive normalized law therefore has strictly smaller cost but the same optimal lower bound, a contradiction."))),
                    DescribeRole.Theorem))));
    }
}
