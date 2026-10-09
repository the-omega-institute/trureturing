using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Dyadic;

internal sealed class ComplementaryDyadicSecondSupportDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) => Par(Seq(a, Sp, Land, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, Rightarrow, Sp, b));
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(x, n);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform low-side affine bound for the dyadic cost on Fin(2^a+1).",
        H("Complementary Dyadic Second Support"),
        Blocks(Describe.Lean(DescribeId.Create("low-side-second-support"),
            DeclarationHandle.Create(
                "D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.result"),
            H("Low-side supporting inequality"), StatementSource.FromAuthor(ResultFormula()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")),
            Blocks(
                Paragraph(Text("Let a>=3, B=2^a and m=B+1. For every nonnegative real law p "
                    + "on Fin(m) whose coordinates sum to one, put t=min_i p(i). If "
                    + "t<=(B-1)/B^2, then L(p)>=[B(a+2)+2B^2]t-2(B-1). Here R(p,d) "
                    + "and L(p) are the residual and cost of Dyadic Cost Support Lines: "
                    + "R(p,d)=2^d-sum_i floor(2^d p(i)), and L(p)=sum_d R(p,d)/2^d. "
                    + "The nonnegative tail series converges on the real probability simplex. "
                    + "Zero coordinates and terminating dyadic expansions are included.")),
                Paragraph(Text("The classical Knuth-Yao DDG expression, recalled by Lumbroso "
                    + "in Section 2.1 and used in Saad, Freer, Rinard and Mansinghka's "
                    + "Fast Loaded Dice Roller (arXiv:2003.03830), supplies the cost model. "
                    + "Those sources do not supply this affine inequality on the complementary "
                    + "simplex. The Mersenne support inequalities supply the comparison used "
                    + "in the lowest interval.")),
                Paragraph(Text("Write f_d(x)=x-floor(2^d x)/2^d. Each f_d is nonnegative, "
                    + "and normalization gives sum_i f_d(p(i))=R(p,d)/2^d. Thus every "
                    + "finite collection of complete depth layers gives a lower bound for L. "
                    + "When t<=(B-3)/B^2, two merges reduce the law to B-1 labels. "
                    + "A merge preserves normalization and the common lower bound t, and "
                    + "floor superadditivity decreases every residual. The Mersenne second "
                    + "support line then dominates the required bound.")),
                Paragraph(Text("For (B-3)/B^2<t<=(B-2)/B^2, every atom is below 3/B. "
                    + "All floors before depth a-1 vanish. At depth a-1, every floor is "
                    + "at most one, and at most one atom can be at least 2/B: two such "
                    + "atoms and the remaining B-1 atoms would have total mass above one. "
                    + "The first a layers therefore contribute at least a-2/B, which "
                    + "dominates the affine bound throughout this interval.")),
                Paragraph(Text("For (B-2)/B^2<t<=(B-1)/B^2, put delta=1-Bt and "
                    + "S={i:Bp(i)<1}, with N=|S|. Then 1<=B delta<2. Normalization "
                    + "gives sum_i(1-Bp(i))=1, while positive deficits occur only in S "
                    + "and each is at most delta, so N delta>=1. The first a layers "
                    + "contribute exactly a. For i in S and 0<=j<a, the next floors "
                    + "equal 2^j-1; these a layers contribute at least k/B per atom, "
                    + "where k=2-2/B-a delta>=0. Their total is at least Nk/B.")),
                Paragraph(Text("The factorization "
                    + "k-B delta[4-(2B+a+2)delta]="
                    + "(B delta-1)[(2B+a+2)B delta-2(B-1)]/B>=0, together with "
                    + "N delta>=1, gives Nk/B>=4-(2B+a+2)delta. Adding the first "
                    + "a layers yields exactly [B(a+2)+2B^2]t-2(B-1). The upper "
                    + "endpoint is included in this argument.")),
                Paragraph(Text("This theorem concerns the low interval only. It does not "
                    + "establish the same inequality above (B-1)/B^2, classify equality, "
                    + "compute the optimum first coefficient, or assert an effective "
                    + "sampler for every arbitrary real law."))),
            DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var a = V("a"); var p = V("p"); var i = V("i"); var t = V("t");
        var b = Pow(D(2), a);
        var indices = Call("Fin", Par(Seq(b, Sp, Plus, Sp, D(1))));
        var law = Seq(indices, Sp, To, Sp, Real);
        var sum = Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, indices)), Call("p", i));
        var assumptions = And(Par(All(i, indices, Seq(D(0), Sp, Le, Sp, Call("p", i)))),
            Equal(sum, D(1)));
        var threshold = Div(Par(Seq(b, Sp, Minus, Sp, D(1))), Pow(b, D(2)));
        var coefficient = Par(Seq(b, Sp, Par(Seq(a, Sp, Plus, Sp, D(2))),
            Sp, Plus, Sp, D(2), Sp, Pow(b, D(2))));
        var inequality = Seq(coefficient, Sp, t, Sp, Minus, Sp, D(2), Sp,
            Par(Seq(b, Sp, Minus, Sp, D(1))), Sp, Le, Sp, Call("L", p));
        return Disp(All(a, Nat, Imp(Seq(D(3), Sp, Le, Sp, a),
            All(p, law, Imp(assumptions, All(t, Real, Imp(Equal(t, Call("min", p)),
                Imp(Seq(t, Sp, Le, Sp, threshold), inequality))))))));
    }
}
