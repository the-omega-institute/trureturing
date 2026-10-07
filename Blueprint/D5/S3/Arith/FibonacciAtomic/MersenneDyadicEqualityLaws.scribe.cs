using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class MersenneDyadicEqualityLawsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/MersenneDyadicEqualityLaws.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(Formula x, Formula type, Formula body) =>
        Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));
    private static Formula Or(Formula a, Formula b) => Par(Seq(a, Sp, Lor, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, Rightarrow, Sp, b));
    private static Formula Iff(Formula a, Formula b) => Par(Seq(a, Sp, Leftrightarrow, Sp, b));
    private static Formula IndexedSum(Formula i, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, domain)), body);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality cases of both affine dyadic-cost bounds on Mersenne probability simplices.",
        H("Mersenne Dyadic Equality Laws"),
        Blocks(Describe.Lean(DescribeId.Create("equality-laws"),
            DeclarationHandle.Create(Prefix + "result"), H("Both equality classifications"),
            StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Fix a natural number h>=2, M=2^h and m=M-1. Let p be any "
                + "nonnegative real probability vector on Fin(m), and let t be its smallest "
                + "coordinate. L is the dyadic cost defined in Dyadic Cost Support Lines: "
                + "the sum over d>=0 of (2^d-sum_i floor(2^d p(i)))/2^d. "
                + "Put a=hM-2 and b=(h+2)M-2. The point law delta(j) has coordinate one at j "
                + "and zero elsewhere; v(j)(i)=(1+delta(j)(i))/M. The uniform law u has all "
                + "coordinates 1/m. For a natural number r and an index j, define s(r,j)(j) "
                + "as 1/m+(M-2)/(m M^(r+1)), and every other coordinate as "
                + "1/m-1/(m M^(r+1)).")),
                Paragraph(Text("The first support equality L(p)=a t holds exactly for a point "
                    + "law or a biased law v(j). The second support equality L(p)=b t-2 "
                    + "holds exactly for u or one of the finite staircase laws s(r,j). "
                    + "Both directions hold for every real probability vector, including "
                    + "zero atoms and terminating dyadic expansions. At r=0 the staircase "
                    + "law equals v(j).")),
                Paragraph(Text("The dyadic cost bounds Shannon entropy. For a positive "
                    + "coordinate x, choose the first depth k with 2^k x>=1. Earlier floors "
                    + "vanish, so its dyadic series is at least kx; monotonicity of the "
                    + "logarithm gives -x log(x)/log(2)<=kx. Summation gives the entropy "
                    + "bound, with zero coordinates contributing zero. When "
                    + "0<t<=1/M, put w(i)=(p(i)-t)/(1-mt) and c=Mt. The law p is the "
                    + "convex combination of delta(j) and v(j) with respective weights "
                    + "(1-c)w(j) and c w(j). Strict concavity of -x log(x), applied in "
                    + "each coordinate, forces c=1 and all active biased vertices to "
                    + "coincide if the first support equality holds. At t=0, zero cost "
                    + "forces a point law. Above 1/M the second support line is strictly "
                    + "stronger than the first.")),
                Paragraph(Text("For a high-interval law set q(i)=Mp(i)-1. Its coordinates "
                    + "are nonnegative and sum to one, and L(p)=h+L(q)/M. The second "
                    + "support defect is divided by M under the inverse transformation. "
                    + "If p is nonuniform, its distance from the uniform law grows by "
                    + "M under each forward transformation, so a finite first exit from "
                    + "the high interval exists. At exit the two support inequalities "
                    + "force the minimum coordinate to equal 1/M; the first equality "
                    + "classification then yields v(j). Inverting the finite sequence "
                    + "gives precisely s(r,j). For the reverse implication, the explicit "
                    + "biased cost and the same scaling identity prove every staircase "
                    + "equality by induction. The uniform law is a fixed point and has "
                    + "cost hM/m."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var h = V("h"); var p = V("p"); var i = V("i");
        var j = V("j"); var r = V("r"); var t = V("t");
        var M = new Formula.Power(D(2), h);
        var m = Par(Seq(M, Sp, Minus, Sp, D(1)));
        var indices = Call("Fin", m);
        var laws = Seq(indices, Sp, To, Sp, Real);
        var a = Par(Seq(h, Sp, M, Sp, Minus, Sp, D(2)));
        var b = Par(Seq(Par(Seq(h, Sp, Plus, Sp, D(2))), Sp, M, Sp, Minus, Sp, D(2)));
        var assumptions = And(Par(All(i, indices, Seq(D(0), Sp, Le, Sp, Call("p", i)))),
            Equal(IndexedSum(i, indices, Call("p", i)), D(1)));
        var first = Iff(Equal(Call("L", p), Seq(a, Sp, t)),
            Ex(j, indices, Or(Equal(p, Call("delta", j)), Equal(p, Call("v", j)))));
        var second = Iff(Equal(Call("L", p), Seq(b, Sp, t, Sp, Minus, Sp, D(2))),
            Or(Equal(p, V("u")), Ex(r, Nat, Ex(j, indices, Equal(p, Call("s", r, j))))));
        return Disp(All(h, Nat, Imp(Seq(D(2), Sp, Le, Sp, h), All(p, laws,
            Imp(assumptions, All(t, Real, Imp(Equal(t, Call("min", p)), And(first, second))))))));
    }
}
