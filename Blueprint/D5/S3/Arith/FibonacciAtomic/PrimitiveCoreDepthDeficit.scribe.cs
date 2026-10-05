using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class PrimitiveCoreDepthDeficitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/PrimitiveCoreDepthDeficit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique nonnegative exit cores relate the golden norm to Fibonacci depth.",
        H("Primitive Composition Cores and Depth Deficits"),
        Blocks(Describe.Lean(
            DescribeId.Create("primitive-core-depth-deficit"),
            DeclarationHandle.Create(Prefix + "result"),
            H("The unique exit core and its logarithmic bounds"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every nonzero pair x=(a,b) of natural numbers with "
                    + "gcd(a,b)=1, there is a unique natural depth j and natural core "
                    + "c=(r,s) with r>s and x=M^j(c). Here M(a,b)=(b,a+b) and "
                    + "q(a,b)=2a+3b are the Fibonacci step and quantity. The norm Q(x) "
                    + "is the golden integer norm of a+b phi: a^2+ab-b^2. "
                    + "The core is primitive, and D=abs(Q(x))=r^2+rs-s^2.")),
                Paragraph(Text("The depth deficit L(x)=log(q(x))/log(phi)-j uses the "
                    + "natural real logarithm and phi=(1+sqrt(5))/2. Both displayed "
                    + "bounds concern this same pair, core, depth and norm. They hold "
                    + "for every nonzero primitive nonnegative composition, including "
                    + "pairs with a zero coordinate.")),
                Paragraph(Text("When b>=a, the inverse step (b-a,a) is nonnegative "
                    + "and decreases q by a+b. It therefore reaches the exit section "
                    + "r>s. The forward step is injective, and every positive-length "
                    + "forward image has its second coordinate at least its first. "
                    + "Cancelling a common iterate proves uniqueness. Each step "
                    + "preserves the gcd and reverses the sign of the golden norm.")),
                Paragraph(Text("The identities D-r^2=s(r-s) and "
                    + "5r^2-4D=(r-2s)^2 give r^2<=D<=(5/4)r^2. The quantity "
                    + "along the orbit is r F_(j+3)+s F_(j+4). Since 0<=s<r, "
                    + "it lies between r F_(j+3) and r F_(j+5). The standard "
                    + "Fibonacci and golden-ratio identity gives "
                    + "phi^n<=F_(n+2)<=phi^(n+1), so the quantity lies between "
                    + "r phi^(j+1) and r phi^(j+4). Taking logarithms and "
                    + "dividing by the positive log(phi) yields the deficit bounds."))),
            DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var x = F.Id("x"); var j = F.Id("j"); var r = F.Id("r"); var s = F.Id("s");
        var d = F.Id("D"); var phi = F.Id("phi");
        var k = F.Id("k"); var u = F.Id("u"); var v = F.Id("v");
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula lp = Call("log", phi);
        Formula ld = Call("log", d);
        Formula deficit = Call("L", x);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, x, InMacro, new Formula.Power(nat, D(2)), Comma,
                x, Neq, Seq(Open, D(0), Comma, D(0), Close), Land, Sp,
                Call("gcd", new Formula.Subscript(x, D(1)),
                    new Formula.Subscript(x, D(2))), Eq, D(1), Rightarrow),
            Seq(Exists, Sp, j, InMacro, nat, Comma, r, Comma, s, InMacro, nat, Comma,
                r, Gt, s, Ge, D(0), Comma,
                x, Eq, Call("iterate", F.Id("M"), j, Seq(Open, r, Comma, s, Close))),
            Seq(Forall, Sp, k, InMacro, nat, Comma, u, Comma, v, InMacro, nat, Comma,
                u, Gt, v, Ge, D(0), Land, Sp, x, Eq,
                Call("iterate", F.Id("M"), k, Seq(Open, u, Comma, v, Close)),
                Rightarrow, Sp, k, Eq, j, Land, Sp, u, Eq, r, Land, Sp, v, Eq, s),
            Seq(Call("gcd", r, s), Eq, D(1), Comma, d, Eq, Call("abs", Call("Q", x)),
                Eq, new Formula.Power(r, D(2)), Plus, r, Cdot, Sp, s, Minus,
                new Formula.Power(s, D(2))),
            Seq(new Formula.Fraction(Seq(ld, Minus,
                    Call("log", new Formula.Fraction(D(5), D(4)))), Seq(D(2), Cdot, Sp, lp)),
                Plus, D(1), Le, deficit, Le,
                new Formula.Fraction(ld, Seq(D(2), Cdot, Sp, lp)), Plus, D(4))
        ]));
    }
}
