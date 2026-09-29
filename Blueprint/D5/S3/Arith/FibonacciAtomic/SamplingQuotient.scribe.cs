using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class SamplingQuotientDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Fibonacci samples determine exactly the coarse time observations; a nonzero sampling kernel prevents an autonomous one-step update.",
        H("Fibonacci Sampling and the Coarse Time Quotient"),
        Blocks(Describe.Lean(
            DescribeId.Create("fibonacci-sampling-quotient"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/SamplingQuotient.sampling_quotient"),
            H("Coarse time equivalence and the one-step obstruction"),
            StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let n be a positive natural number, including n=1, and let m be at least two. "
                    + "The time family t : Fin(m) -> N is strictly increasing. Set s=t(0), "
                    + "g=gcd(t(i)-s : i is nonzero), and O(x)(i)=r(t(i),x). "
                    + "All states x=(a,b) belong to (Z/nZ)^2 and r(k,x)=F(k)a+F(k+1)b, "
                    + "where F(0)=0 and F(1)=1. The step S(a,b)=(b,a+b) has matrix M=[[0,1],[1,1]]. "
                    + "Every occurrence of a time observation refers to this same state and keeps its time label. "
                    + "In the displayed formula, adjacentRows(s) has rows (F(s),F(s+1)) and "
                    + "(F(s+1),F(s+2)); M3 and r3 denote M and r over Z/3Z, and I is the identity matrix.")),
                Paragraph(Text("Write u(j,x)=r(s+jg,x) and L=trace(M^g). For every natural j and every x, "
                    + "u(j+2,x)=L*u(j+1,x)-(-1)^g*u(j,x). The kernel of O equals the joint kernel of "
                    + "r(s,-) and r(s+g,-). In the shifted coordinates (a',b')=S^s(z), it is exactly "
                    + "b'=0 and F(g)*a'=0. Consequently O(x)=O(y) if and only if u(j,x)=u(j,y) "
                    + "for all natural j. The first two coarse readings therefore determine the entire coarse sequence.")),
                Paragraph(Text("For every function Phi on the sample space, the identity O(S(x))=Phi(O(x)) "
                    + "for all states implies that O(z)=0 entails O(S(z))=0. The pair "
                    + "x -> (r(s,x),r(s+1,x)) is injective: its matrix has determinant (-1)^(s+1). "
                    + "Thus a state in a stable sampling kernel must be zero. If any nonzero state lies "
                    + "in the sampling kernel, there is no such Phi, even without a linearity assumption on Phi.")),
                Paragraph(Text("Over Z/3Z, M^4=2I and r(4j,x)=2^j*b for every natural j. In particular "
                    + "r(8j,x)=b and r(8j+4,x)=2b. The states (0,0) and (1,0) agree at every "
                    + "time 4j, but their time-one readings are respectively 0 and 1, which are distinct.")),
                Paragraph(Text("For this modulus define O4(x)=(r(0,x),r(4,x)). There exists a function Psi "
                    + "with O4(S^4(x))=Psi(O4(x)) for every x; multiplication of both sample coordinates "
                    + "by 2 gives one. There is no function Phi with O4(S(x))=Phi(O4(x)) for all x. "
                    + "The theorem explicitly negates the implication from the existence of the four-step "
                    + "update to the existence of the one-step update: in this example the coarse sample "
                    + "closes under the four-step clock but not under the one-step clock.")),
                Paragraph(Text("Cayley-Hamilton gives the coarse recurrence. Fibonacci divisibility places "
                    + "the two-reading kernel inside the sampling kernel. Their equal finite cardinalities, "
                    + "both gcd(n,F(g)), give equality. Applying that equality to differences yields the "
                    + "coarse observation equivalence. The invertible Fibonacci step gives adjacent-reading "
                    + "injectivity and the obstruction to a one-step update."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Pow(Formula a, Formula b) => Seq(a, Caret, Grp(b));
    private static Formula Both(params Formula[] xs) =>
        Seq(xs.SelectMany((x, i) => i == 0 ? new[] { Par(x) } : new[] { Sp, Land, Sp, Par(x) }).ToArray());
    private static Formula ResultFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z"), j = F.Id("j");
        Formula s = F.Id("s"), g = F.Id("g");
        Formula R(Formula k, Formula a) => Call("r", k, a);
        Formula O(Formula a) => Call("O", a);
        Formula U(Formula k, Formula a) => Call("u", k, a);
        Formula all(Formula a, Formula p) => Seq(Forall, Sp, a, Comma, Sp, p);
        Formula iff(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
        Formula kernel = all(z, Both(
            iff(Equal(O(z), D(0)), Both(Equal(R(s, z), D(0)), Equal(R(Add(s, g), z), D(0)))),
            iff(Equal(O(z), D(0)), Both(Equal(Call("snd", Call("iterate", F.Id("S"), s, z)), D(0)),
                Equal(Multiply(Call("fib", g), Call("fst", Call("iterate", F.Id("S"), s, z))), D(0))))));
        Formula coarse = all(x, all(y, iff(Equal(O(x), O(y)), all(j, Equal(U(j, x), U(j, y))))));
        Formula recurrence = all(x, all(j, Equal(U(Add(j, D(2)), x),
            Subtract(Multiply(F.Id("L"), U(Add(j, D(1)), x)),
                Multiply(Pow(Par(Seq(Minus, D(1))), g), U(j, x))))));
        Formula update = all(x, Equal(O(Call("S", x)), Call("Phi", O(x))));
        Formula obstruction = Seq(
            Par(Seq(Exists, Sp, z, Comma, Sp, Both(Seq(z, Sp, Neq, Sp, D(0)), Equal(O(z), D(0))))),
            Sp, Implies, Sp, Neg, Par(Seq(Exists, Sp, F.Id("Phi"), Comma, Sp, update)));
        Formula update4(Formula step, string name) => all(x,
            Equal(Call("O4", Call("iterate", F.Id("S"), step, x)), Call(name, Call("O4", x))));
        Formula existsUpdate(Formula step, string name) =>
            Seq(Exists, Sp, F.Id(name), Comma, Sp, update4(step, name));
        Formula c4 = existsUpdate(D(4), "Psi"), c1 = existsUpdate(D(1), "Phi");
        Formula modThree = Both(
            Equal(Pow(F.Id("M3"), D(4)), Multiply(D(2), F.Id("I"))),
            all(j, all(x, Equal(Call("r3", Multiply(D(4), j), x), Multiply(Pow(D(2), j), Call("snd", x))))),
            all(j, all(x, Both(Equal(Call("r3", Multiply(D(8), j), x), Call("snd", x)),
                Equal(Call("r3", Add(Multiply(D(8), j), D(4)), x), Multiply(D(2), Call("snd", x)))))),
            all(j, Equal(Call("r3", Multiply(D(4), j), Call("pair", D(0), D(0))),
                Call("r3", Multiply(D(4), j), Call("pair", D(1), D(0))))),
            Equal(Call("r3", D(1), Call("pair", D(0), D(0))), D(0)),
            Equal(Call("r3", D(1), Call("pair", D(1), D(0))), D(1)),
            Seq(D(0), Sp, Neq, Sp, D(1)),
            c4, Seq(Neg, Par(c1)), Seq(Neg, Par(Seq(Par(c4), Sp, Implies, Sp, Par(c1)))));
        return Disp(Both(recurrence, kernel, coarse,
            Seq(Forall, Sp, F.Id("Phi"), Comma, Sp, Par(update), Sp, Implies, Sp,
                all(z, Seq(Equal(O(z), D(0)), Sp, Implies, Sp, Equal(O(Call("S", z)), D(0))))),
            Call("Injective", Seq(x, Sp, Mapsto, Sp, Par(Seq(R(s, x), Comma, R(Add(s, D(1)), x))))),
            Equal(Call("det", Call("adjacentRows", s)), Pow(Par(Seq(Minus, D(1))), Add(s, D(1)))),
            obstruction,
            modThree));
    }
}
