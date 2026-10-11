using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class CommonResiduePrecisionFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/CommonResiduePrecisionFamily.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula EqOf(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula LtOf(Formula x, Formula y) => Seq(x, Sp, Lt, Sp, y);
    private static Formula LeOf(Formula x, Formula y) => Seq(x, Sp, Leq, Sp, y);
    private static Formula Both(params Formula[] clauses) => Seq(clauses.SelectMany((clause, i) =>
        i == 0 ? new[] { Par(clause) } : new[] { Sp, Land, Sp, Par(clause) }).ToArray());
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("common-residue-precision-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common integer family approaches density ratio one in the real embedding while retaining prescribed prime precision.",
        H("Common Residue Classes for Source Density Precision"),
        Blocks(
            Paragraph(Text("Let E=F(3k-2), A=F(3k-1), D=F(3k), and L=F(3k+1), "
                + "using the coefficients of SourceDensityMonotonicity. For k>=1, E,A are positive and D=E+A is even. "
                + "The integer m is j+1. Legal tree grids have 1<=m<=t; auxiliary seed values need not lie on that grid.")),
            Def("numerator", "Integer numerator", "numerator(k,t,m) is (t-m+1) times the product "
                + "of At+Em-r over 0<=r<E, times the product of Dt+Am-s over 0<=s<A. "
                + "The arguments t,m are integers, and both empty products equal one."),
            Def("denominator", "Integer denominator", "denominator(k,t,m) is 2^D m times "
                + "the product of 2Lt+2Dm-2D+2h-1 over 0<=h<D. This is the original integer "
                + "denominator, whose prime valuations need not vanish."),
            Def("G", "Quadratic coefficient", "G(k)=A D (E-1)! (A-1)!, with natural subtraction."),
            Def("K", "Linear coefficient", "K(k)=2^D times the product of 2h+3 over 0<=h<D."),
            Def("ratio", "Rational adjacent ratio", "ratio(k,t,m) is numerator(k,t,m) divided by "
                + "denominator(k,t,m) in the rational numbers, with natural t,m. On 1<=m<=t its "
                + "real embedding equals q(k,m-1,t), hence the ratio of the two actual source densities."),
            Describe.Lean(DescribeId.Create("common-residue-precision-family"),
                DeclarationHandle.Create(Prefix + "result"), H("Joint real and prime precision"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Here N,Q,R denote the natural, rational and real numbers. "
                        + "Rational values in real expressions use the canonical embedding. "
                        + "vpN(p,B) is padicValNat p B and vp(p,x) is padicValRat p x. "
                        + "PairInjective(t,j) means that equal pairs (t(r),j(r))=(t(s),j(s)) force r=s. "
                        + "RealRatioFamily(k,t,j) is N mapped to the real embedding of ratio(k,t(N),j(N)+1). "
                        + "sourceDensity is the actual substitution-image density in its complete composition fiber.")),
                    Paragraph(Text("Put V=G K^2 and Z=V B. Removing the two zero endpoint factors "
                        + "from the numerator at (KZ,GKZ^2) leaves a factor congruent to V modulo Z. "
                        + "The denominator has the same quadratic factor and the same residual constant. "
                        + "Thus one seed has the required numerator divisibility even at primes dividing G or K. "
                        + "The modulus B times its true denominator preserves that denominator's exact prime valuations.")),
                    Paragraph(Text("Increase m in this residue class and take the first point in the t residue class "
                        + "strictly to the right of the corresponding crossing root. The root bound guarantees legality; "
                        + "the distance is at most the fixed modulus. The logarithmic derivative on this interval "
                        + "is bounded above by (D+1)/m, so the positive logarithmic error tends to zero. "
                        + "The minority coordinates strictly increase and therefore distinguish all the pairs. "
                        + "No zero rational difference enters the valuation argument, since every ratio is strictly greater than one.")),
                    Paragraph(Text("The construction is a consequence of the repository's source-density theory "
                        + "and the standard finite-product, congruence and prime-valuation identities. "
                        + "Fixed finite precision does not assert exact equality or classify possible integer ties."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var k = V("k"); var b = V("B"); var t = V("t"); var j = V("j");
        var n = V("n"); var p = V("p");
        var tn = new Formula.Apply(t, [n]); var jn = new Formula.Apply(j, [n]);
        var q = Call("ratio", k, tn, Add(jn, D(1)));
        var density = new Formula.Fraction(Call("sourceDensity", k, tn, Add(jn, D(1))),
            Call("sourceDensity", k, tn, jn));
        var primePrecision = Seq(Forall, Sp, p, Sp, InMacro, Sp, V("N"), Comma, Sp,
            Par(Both(Call("Prime", p), Call("Dvd", p, b))), Sp, Implies, Sp,
            LeOf(Call("vpN", p, b), Call("vp", p, Subtract(q, D(1)))));
        var each = Seq(Forall, Sp, n, Sp, InMacro, Sp, V("N"), Comma, Sp,
            Both(LeOf(D(1), tn), LtOf(jn, tn), LtOf(D(1), q), EqOf(q, density), primePrecision));
        return Disp(Seq(Forall, Sp, k, Comma, b, Sp, InMacro, Sp, V("N"), Comma, Sp,
            Par(Both(LeOf(D(1), k), LeOf(D(2), b))), Sp, Implies, Sp,
            Exists, Sp, t, Comma, j, Sp, Colon, Sp, V("N"), Sp, To, Sp, V("N"), Comma, Sp,
            Both(Call("PairInjective", t, j), each,
                Call("Tendsto", Call("RealRatioFamily", k, t, j), Call("atTop"), Call("nhds", D(1))))));
    }
}
