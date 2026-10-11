using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class MovingRootDisplacementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/MovingRootDisplacement.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. xs]);
    private static Formula Mul(params Formula[] xs) => Seq(xs.Select(Par).ToArray());
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sq(Formula x) => new Formula.Power(Par(x), D(2));
    private static Formula Abs(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula LtOf(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Both(params Formula[] xs) => Seq(xs.SelectMany((x, i) =>
        i == 0 ? new[] { Par(x) } : new[] { Sp, Land, Sp, Par(x) }).ToArray());
    private static Formula All(string name, string type, Formula body) =>
        Seq(Forall, Sp, V(name), Sp, InMacro, Sp, V(type), Comma, Sp, body);
    private static Formula Ex(string name, string type, Formula body) =>
        Seq(Exists, Sp, V(name), Sp, InMacro, Sp, V(type), Comma, Sp, body);
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("moving-root-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common quantitative expansion controls both moving test points and the unique density root.",
        H("Additive Displacement of Fibonacci Source Density Roots"),
        Blocks(
            Paragraph(Text("E, A, D, L, H, q and c are the existing Fibonacci finite-product quantities. "
                + "Natural k is at least one and j is a natural minority index. Real arguments are "
                + "auxiliary finite-product parameters. The estimates concern fixed j; constants and "
                + "tail thresholds may depend on j. N and R denote natural and real numbers.")),
            Def("kappa", "Cassini coefficient", "For every natural k, kappa(k)=1/(L(k)A(k)D(k))."),
            Def("sigma", "Bounded displacement", "For every natural k, "
                + "sigma(k)=D(k)/L(k)+E(k)/(2A(k))+A(k)/(2D(k))."),
            Def("B", "First normalized moment", "For natural k,j, B(k,j)=sigma(k)+kappa(k)(j+1/2)."),
            Describe.Lean(DescribeId.Create("moving-root-quantitative-expansion"),
                DeclarationHandle.Create(Prefix + "quantitative_expansion"), H("Uniform finite-product remainder"),
                StatementSource.FromAuthor(Expansion()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The numerator offsets are (Ej+i)/A for 1<=i<=E "
                    + "and (Aj+s)/D for 1<=s<=A; denominator offsets are (Dj+h-1/2)/L "
                    + "for 0<=h<D, including the negative half-step at j=h=0. Each has absolute "
                    + "value at most j+1. The logarithmic error per normalized factor is at most "
                    + "the square of its offset divided by t squared, using the pinned Mathlib "
                    + "complex logarithm remainder restricted to real inputs. Cassini supplies the "
                    + "first moment B, and E+A+D=2D gives the displayed exact coefficient. This "
                    + "estimate is consumed by the common moving-point crossing proof."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("moving-root-additive-displacement"),
                DeclarationHandle.Create(Prefix + "root_displacement"), H("Fixed-index additive root displacement"),
                StatementSource.FromAuthor(Displacement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The root is the unique legal real root of the existing ratio q. "
                    + "Writing M=(j+1)/c and b=j+3, the proof controls log q(M+j-B+s)-s/M for "
                    + "all |s|<=1 with error at most R D/M^2, where "
                    + "R=(b+1)^2+2b(j+b+1)+8(j+1)^2. Since c<=4^(-D) and Dc tends to zero, "
                    + "C=(R+1)/(j+1) and a common tail make the points M+j-B-CDc and M+j-B+CDc "
                    + "legal and put their q values strictly below and above one. The frozen "
                    + "strict monotonicity then traps the root between them. The same tail makes "
                    + "the exact logarithmic root equation valid. These are repository-derived "
                    + "finite-product estimates; no literature novelty is claimed. No assertion "
                    + "about the continuous-minimizer comparison or joint uniformity in j,k is made."))),
                DescribeRole.Theorem))));

    private static Formula Expansion()
    {
        var k = V("k"); var j = V("j"); var t = V("t");
        var jp = Add(j, D(1));
        var bound = Div(Mul(D(2), Call("D", k), Sq(jp)), Sq(t));
        var error = Abs(Subtract(Call("log", Div(Call("H", k, j, t), Call("c", k))),
            Div(Call("B", k, j), t)));
        return Disp(All("k", "N", Imp(Le(D(1), k), All("j", "N", All("t", "R",
            Imp(Le(Mul(D(2), jp), t), Le(error, bound)))))));
    }

    private static Formula Displacement()
    {
        var j = V("j"); var k = V("k"); var t = V("t"); var x = V("x");
        var constant = V("C"); var threshold = V("K"); var jp = Add(j, D(1));
        var m = Div(jp, Call("c", k));
        var unique = All("x", "R", Imp(Le(jp, x), Imp(EqOf(Call("q", k, j, x), D(1)), EqOf(x, t))));
        var displacement = Le(Abs(Subtract(t, Subtract(Add(m, j), Call("B", k, j)))),
            Mul(constant, Call("D", k), Call("c", k)));
        var rootError = Le(Abs(Add(Call("log", Div(Subtract(t, j), m)), Div(Call("B", k, j), t))),
            Div(Mul(D(2), Call("D", k), Sq(jp)), Sq(t)));
        var root = Ex("t", "R", Both(Le(jp, t), EqOf(Call("q", k, j, t), D(1)),
            unique, displacement, rootError));
        var tail = All("k", "N", Imp(Le(threshold, k), root));
        var thresholdClaim = Ex("K", "N", Both(Le(D(1), threshold), tail));
        return Disp(All("j", "N", Ex("C", "R", Both(LtOf(D(0), constant), thresholdClaim))));
    }
}
