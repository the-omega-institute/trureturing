using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class SourceDensityMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula EqOf(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula LtOf(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula LeOf(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Both(params Formula[] clauses) => Seq(clauses.SelectMany((clause, i) =>
        i == 0 ? new[] { Par(clause) } : new[] { Sp, Land, Sp, Par(clause) }).ToArray());
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("source-density-monotonicity-" + (name == "a" ? "coordinate-a" : name.ToLowerInvariant())),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three affine logarithmic blocks admit a joint lower bound under a squared determinant identity.",
        H("Fibonacci Source Density Ratios and Logarithmic Compensation"),
        Blocks(
            Paragraph(Text("F denotes the natural Fibonacci sequence with F(0)=0 and F(1)=1. "
                + "Fix natural k>=1 and j. Put d=3k. Nonintegral t is an auxiliary real "
                + "parameter of finite products; it does not represent a nonintegral number of tree leaves.")),
            Def("E", "First numerator length", "E(k)=F(3k-2), with truncated natural subtraction."),
            Def("A", "Second numerator length", "A(k)=F(3k-1)."),
            Def("D", "Denominator length", "D(k)=F(3k)."),
            Def("L", "Total composition coefficient", "L(k)=F(3k+1)."),
            Def("a", "First affine target coordinate", "a(k,j,t)=A(k)t+E(k)j."),
            Def("b", "Second affine target coordinate", "b(k,j,t)=D(k)t+A(k)j."),
            Def("n", "Total affine target coordinate", "n(k,j,t)=L(k)t+D(k)j."),
            Def("rising", "Rising finite product", "rising(x,m) is the product of x+i over "
                + "natural 0<=i<m. The empty product is one."),
            Def("H", "Finite-product factor", "H(k,j,t)=rising(a+1,E) rising(b+1,A) "
                + "/ (4^D rising(n-1/2,D)), where all coefficients and coordinates have the same k,j,t."),
            Def("q", "Real extension", "q(k,j,t)=(t-j)H(k,j,t)/(j+1)."),
            Def("c", "Leading coefficient", "c(k)=A(k)^E(k) D(k)^A(k)/(4^D(k) L(k)^D(k))."),
            Def("g", "Logarithmic derivative", "g(k,j,t)=1/(t-j)+A sum(1/(a+1+i),i<E) "
                + "+D sum(1/(b+1+i),i<A)-L sum(1/(n-1/2+i),i<D)."),
            Def("lowerEnvelope", "Three-block lower envelope", "The lower envelope is "
                + "1/(t-j)-(j+1/2)/(LADt^2)-AE/(2a(a+E))-DA/(2b(b+A)) "
                + "-LD/((n-1/2)(n+D-1/2)). Its coordinates share the same k,j,t."),
            Describe.Lean(DescribeId.Create("source-density-logarithmic-compensation"),
                DeclarationHandle.Create(Prefix + "logarithmic_compensation"),
                H("Joint logarithmic compensation"),
                StatementSource.FromAuthor(CompensationFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive e,a,d,l,t and nonnegative j, assume d=e+a, "
                    + "l=a+d and (a^2-de)^2=1. The weighted increments of the three affine "
                    + "logarithms have lower bound -(j+1/2)/(ladt^2). Along the unit interval, "
                    + "their derivative is -t(j+s) divided by the product of the three affine "
                    + "coordinates. Adding (js+s^2/2)/(ladt^2) makes the derivative nonnegative, "
                    + "so comparing the endpoints gives the bound."))), DescribeRole.Theorem))));

    private static Formula CompensationFormula()
    {
        var e = V("e"); var a = V("a"); var d = V("d"); var l = V("l");
        var t = V("t"); var j = V("j");
        var half = new Formula.Fraction(D(1), D(2));
        Formula Inc(Formula x, Formula y) => Sub(
            Call("log", Add(Seq(x, t), Seq(y, Par(Add(j, D(1)))))),
            Call("log", Add(Seq(x, t), Seq(y, j))));
        var hypotheses = Both(LtOf(D(0), e), LtOf(D(0), a), LtOf(D(0), d),
            LtOf(D(0), l), EqOf(d, Add(e, a)), EqOf(l, Add(a, d)),
            EqOf(Pow(Par(Sub(Pow(a, D(2)), Seq(d, e))), D(2)), D(1)),
            LtOf(D(0), t), LeOf(D(0), j));
        var bound = new Formula.Fraction(Seq(Neg, Sp, Par(Add(j, half))),
            Seq(l, a, d, Pow(t, D(2))));
        var increments = Sub(Add(Seq(a, Inc(a, e)), Seq(d, Inc(d, a))), Seq(l, Inc(l, d)));
        return Disp(Seq(Forall, Sp, e, Comma, a, Comma, d, Comma, l, Comma, t, Comma, j,
            Sp, InMacro, Sp, V("R"), Comma, Sp, Par(hypotheses), Sp, Implies, Sp,
            LeOf(bound, increments)));
    }
}
