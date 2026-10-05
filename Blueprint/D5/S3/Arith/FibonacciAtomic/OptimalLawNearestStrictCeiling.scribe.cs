using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class OptimalLawNearestStrictCeilingDocument : IScribeDocumentDefinition
{
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, x, Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Imp(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula And(params Formula[] fs) => Seq(Open,
        Seq(fs.SelectMany((f, i) => i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray()), Close);
    private static Formula Ty(string name) => Seq(Mathbb, Grp(F.Id(name)));

    public DocumentDefinition Create()
    {
        var m = F.Id("m"); var p = F.Id("p"); var a = F.Id("a"); var i = F.Id("i");
        var Di = new Formula.Subscript(F.Id("D"), i); var indices = Call("Fin", m);
        var t = Call("inf", Call("range", p));
        var power = new Formula.Power(D(2), Di);
        var hypotheses = And(Seq(D(2), Sp, Le, Sp, m),
            All(a, indices, Seq(D(0), Sp, Lt, Sp, Call("p", a))),
            Equal(Seq(new Formula.Subscript(F.Sum, Seq(a, Sp, InMacro, Sp, indices)), Call("p", a)), D(1)),
            Equal(Call("cost", p), Seq(Call("alpha", m), Sp, Cdot, Sp, t)));
        var ceiling = new Formula.Fraction(Seq(Lfloor, power, Sp, Cdot, Sp, t, Rfloor,
            Sp, Plus, Sp, D(1)), power);
        var statement = All(m, Ty("N"), All(p, Seq(indices, Sp, To, Sp, Ty("R")),
            Imp(hypotheses, All(i, indices,
                Imp(Seq(t, Sp, Lt, Sp, Call("p", i)), Equal(Call("p", i), ceiling))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Every larger atom of an attaining real law is the first strictly higher grid point at its least binary depth.",
            H("Nearest Strict Dyadic Ceilings of Optimal Laws"), Blocks(
                Describe.Lean(DescribeId.Create("result"),
                    DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/OptimalLawNearestStrictCeiling.result"),
                    H("Strict ceiling at the least terminating depth"),
                    StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("The law p is strictly positive and normalized on m labels, with m at least two. Its least mass t is the infimum of its finite range. The dyadic cost divided by t attains the full real infimum alpha(m). For each p(i)>t, D_i is the least natural D for which p(i)=N/2^D for some natural N. Termination supplies this least depth; the Lean statement selects it by Nat.find. The numerator is floor(2^D_i*t)+1, even when 2^D_i*t is an integer.")),
                        Paragraph(Text("Suppose a larger atom violates the formula and choose such an atom j whose least depth d is maximal. Put delta=2^(-d), k=floor(2^d*t), and Q=(k+1)*delta. Let S contain exactly the labels with mass below Q and n be its cardinality. It contains a minimum label and excludes j, so 1<=n<m. Every atom outside S lies on the depth-d grid: an atom of greater least depth obeys its own strict-ceiling formula and would lie at or below Q, while equality would contradict its least depth.")),
                        Paragraph(Text("Atoms inside S have depth-d integer part k. The sum of their fractional parts is an integer R, because the total scaled mass and all outside masses are integers. With f the fractional part of 2^d*t, one has n*f<=R<=n-1. Consequently Q-t>=delta/n. The donor is at least Q+delta, and its least depth implies an odd terminal numerator, so removing delta changes none of its shallower floor counts.")),
                        Paragraph(Text("Choose an attaining n-label law q with minimum u. Normalization gives u<=1/n. Transfer delta from j to S in the proportions q, obtaining a positive normalized law P with every mass at least t+delta*u. The shared dyadic transfer bound gives cost(P)<=alpha(m)*t+delta*alpha(n)*u. Strict growth alpha(n)<alpha(m) makes this less than alpha(m)*(t+delta*u), contradicting the optimal lower bound for P. Thus every larger atom satisfies the displayed strict-ceiling formula."))),
                    DescribeRole.Theorem))));
    }
}
