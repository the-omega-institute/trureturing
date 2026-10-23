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
        "A global affine bound and exact high-side recursion for the dyadic cost on Fin(2^a+1).",
        H("Complementary Dyadic Second Support"),
        Blocks(
            Describe.Lean(DescribeId.Create("high-transform"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.high_transform"),
                H("Affine high-side transformation"), StatementSource.FromAuthor(TransformFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed highTransform denotes high_transform. For a natural a "
                    + "and any real vector p on Fin(2^a+1), "
                    + "high_transform(a,p)(i)=(2^a)^2 p(i)-(2^a-1). The definition "
                    + "does not require positivity or normalization; the scaling theorem "
                    + "below supplies both under its strict minimum hypothesis."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("support-gap"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.support_gap"),
                H("Second support gap"), StatementSource.FromAuthor(GapFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed supportGap denotes support_gap. support_gap(a,p) "
                    + "is the dyadic cost minus "
                    + "[2^a(a+2)+2(2^a)^2] min_i p(i), plus 2(2^a-1). The minimum "
                    + "is over all indices in Fin(2^a+1). Nonnegativity of this gap "
                    + "is equivalent to the second supporting inequality."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("scaled-iterate"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.scaled_iterate"),
                H("Closed affine orbit"), StatementSource.FromAuthor(IterateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The displayed scaledIterate denotes scaled_iterate. "
                    + "scaled_iterate(a,p,k)(i)=1/(2^a+1) "
                    + "+[(2^a)^2]^k[p(i)-1/(2^a+1)]. It is defined for every natural "
                    + "k and every real vector p. The exit theorem restricts to the "
                    + "positive part of this orbit up to its first low-side index."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("low-side-second-support"),
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
                Paragraph(Text("The low-side statement includes its upper endpoint. The global statement below does not "
                    + "classify equality, "
                    + "compute the optimum first coefficient, or assert an effective "
                    + "sampler for every arbitrary real law."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("strict-high-scaling"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.high_scaling"),
                H("Strict high-side scaling"), StatementSource.FromAuthor(HighFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")),
                Blocks(Paragraph(Text("Put B=2^a, t0=(B-1)/B^2, C=B(a+2)+2B^2, "
                    + "d0=2(B-1), H0=a+2-a/B-2/B^2 and D(p)=L(p)-C min(p)+d0. "
                    + "For a>=3 and a normalized law with min(p)>t0, define "
                    + "q(i)=B^2 p(i)-(B-1). Then q is strictly positive and normalized, "
                    + "L(p)=H0+L(q)/B^2 and D(p)=D(q)/B^2. The minimum also transforms "
                    + "as min(q)=B^2 min(p)-(B-1).")),
                    Paragraph(Text("Every p(i) lies between t0 and 1/B. Floors vanish "
                    + "before depth a and equal 2^j-1 at depth a+j, for j<a. These "
                    + "first 2a layers sum to H0. At depth 2a+e, the integer translation "
                    + "formula for floor gives floor(2^(2a+e) p(i))="
                    + "floor(2^e q(i))+(B-1)2^e, so the residual becomes R(q,e). "
                    + "Splitting the convergent series proves the cost identity; the "
                    + "minimum transformation gives the gap identity. The threshold "
                    + "inequality is strict, so this recursion does not apply to its boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-zero-gap"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.uniform_gap_zero"),
                H("Uniform fixed point"), StatementSource.FromAuthor(UniformFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")),
                Blocks(Paragraph(Text("The uniform law u(i)=1/(B+1) is strictly high "
                    + "and is fixed by q. Its gap satisfies D(u)=D(u)/B^2. Since B>=8, "
                    + "this forces D(u)=0. Equivalently, L(u)=[B(a+2)+2]/(B+1)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-high-exit"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.finite_exit"),
                H("Finite positive exit"), StatementSource.FromAuthor(ExitFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")),
                Blocks(Paragraph(Text("Let r_k(i)=1/(B+1)+(B^2)^k[p(i)-1/(B+1)]. "
                    + "Then r_0=p, r_(k+1)=q(r_k), and every r_k has total mass one. "
                    + "Its minimum is 1/(B+1)-(B^2)^k[1/(B+1)-min(p)]. For a "
                    + "nonuniform normalized law, min(p)<1/(B+1). Powers of B^2 "
                    + "therefore force a finite first index n>0 with min(r_n)<=t0. "
                    + "All earlier laws are strictly high. Their successive images are "
                    + "positive, so the first exit remains positive and normalized, with "
                    + "0<min(r_n)<=t0 and D(p)=D(r_n)/(B^2)^n."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("global-second-support"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/FibonacciAtomic/Dyadic/ComplementaryDyadicSecondSupport.global_support"),
                H("Global second supporting inequality"), StatementSource.FromAuthor(GlobalFormula()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Computability/lumbroso2013ddg")),
                Blocks(Paragraph(Text("For every a>=3 and every nonnegative normalized "
                    + "real law on B+1 labels, L(p)>=[B(a+2)+2B^2] min(p)-2(B-1). "
                    + "If the minimum is at most t0, apply the low-side theorem. A "
                    + "uniform law has zero gap. Every other strictly high law exits "
                    + "after finitely many rescalings to a positive low-side law; its "
                    + "nonnegative gap transfers back by a positive factor. Thus no "
                    + "low-side hypothesis remains. Zero atoms and dyadic boundaries "
                    + "are included. This inequality alone does not determine the "
                    + "optimal first coefficient or the full cost envelope."))),
                DescribeRole.Theorem))));

    private static Formula Context(Formula body, bool nonnegative = false)
    {
        var a = V("a"); var p = V("p"); var i = V("i");
        var indices = Call("Fin", Par(Seq(Pow(D(2), a), Sp, Plus, Sp, D(1))));
        var law = Seq(indices, Sp, To, Sp, Real);
        var sum = Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, indices)), Call("p", i));
        Formula assumptions = Equal(sum, D(1));
        if (nonnegative)
            assumptions = And(Par(All(i, indices, Seq(D(0), Sp, Le, Sp, Call("p", i)))), assumptions);
        return All(a, Nat, Imp(Seq(D(3), Sp, Le, Sp, a), All(p, law, Imp(assumptions, body))));
    }

    private static Formula HighFormula()
    {
        var a = V("a"); var p = V("p"); var i = V("i");
        var b = Pow(D(2), a); var q = Call("highTransform", a, p);
        var indices = Call("Fin", Par(Seq(b, Sp, Plus, Sp, D(1))));
        var positive = Par(All(i, indices, Seq(D(0), Sp, Lt, Sp, Call("highTransform", a, p, i))));
        var sum = Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, indices)), Call("highTransform", a, p, i));
        var threshold = Div(Par(Seq(b, Sp, Minus, Sp, D(1))), Pow(b, D(2)));
        var head = Seq(a, Sp, Plus, Sp, D(2), Sp, Minus, Sp, Div(a, b),
            Sp, Minus, Sp, Div(D(2), Pow(b, D(2))));
        return Disp(Context(Imp(Seq(threshold, Sp, Lt, Sp, Call("min", p)),
            And(positive, And(Equal(sum, D(1)), And(
                Equal(Call("L", p), Seq(head, Sp, Plus, Sp, Div(Call("L", q), Pow(b, D(2))))),
                Equal(Call("supportGap", a, p), Div(Call("supportGap", a, q), Pow(b, D(2))))))))));
    }

    private static Formula DefinitionContext(Formula a, Formula p, Formula body)
    {
        var indices = Call("Fin", Par(Seq(Pow(D(2), a), Sp, Plus, Sp, D(1))));
        return All(a, Nat, All(p, Seq(indices, Sp, To, Sp, Real), body));
    }

    private static Formula TransformFormula()
    {
        var a = V("a"); var p = V("p"); var i = V("i"); var b = Pow(D(2), a);
        var indices = Call("Fin", Par(Seq(b, Sp, Plus, Sp, D(1))));
        return Disp(DefinitionContext(a, p, All(i, indices,
            Equal(Call("highTransform", a, p, i), Seq(Pow(b, D(2)), Sp, Call("p", i),
                Sp, Minus, Sp, Par(Seq(b, Sp, Minus, Sp, D(1))))))));
    }

    private static Formula GapFormula()
    {
        var a = V("a"); var p = V("p"); var b = Pow(D(2), a);
        var coefficient = Par(Seq(b, Sp, Par(Seq(a, Sp, Plus, Sp, D(2))),
            Sp, Plus, Sp, D(2), Sp, Pow(b, D(2))));
        return Disp(DefinitionContext(a, p, Equal(Call("supportGap", a, p),
            Seq(Call("L", p), Sp, Minus, Sp, coefficient, Sp, Call("min", p),
                Sp, Plus, Sp, D(2), Sp, Par(Seq(b, Sp, Minus, Sp, D(1)))))));
    }

    private static Formula IterateFormula()
    {
        var a = V("a"); var p = V("p"); var k = V("k"); var i = V("i");
        var b = Pow(D(2), a); var u = Div(D(1), Par(Seq(b, Sp, Plus, Sp, D(1))));
        var indices = Call("Fin", Par(Seq(b, Sp, Plus, Sp, D(1))));
        return Disp(DefinitionContext(a, p, All(k, Nat, All(i, indices,
            Equal(Call("scaledIterate", a, p, k, i), Seq(u, Sp, Plus, Sp,
                Pow(Par(Pow(b, D(2))), k), Sp, Par(Seq(Call("p", i), Sp, Minus, Sp, u))))))));
    }

    private static Formula UniformLaw(Formula a)
    {
        var b = Pow(D(2), a); var i = V("i");
        var indices = Call("Fin", Par(Seq(b, Sp, Plus, Sp, D(1))));
        return Par(Seq(i, Colon, Sp, indices, Sp, Mapsto, Sp,
            Div(D(1), Par(Seq(b, Sp, Plus, Sp, D(1))))));
    }

    private static Formula UniformFormula() => Disp(All(V("a"), Nat,
        Imp(Seq(D(3), Sp, Le, Sp, V("a")),
            Equal(Call("supportGap", V("a"), UniformLaw(V("a"))), D(0)))));

    private static Formula ExitFormula()
    {
        var a = V("a"); var p = V("p"); var n = V("n"); var k = V("k"); var i = V("i");
        var b = Pow(D(2), a);
        var indices = Call("Fin", Par(Seq(b, Sp, Plus, Sp, D(1))));
        var rn = Call("scaledIterate", a, p, n); var rk = Call("scaledIterate", a, p, k);
        var threshold = Div(Par(Seq(b, Sp, Minus, Sp, D(1))), Pow(b, D(2)));
        var before = Par(All(k, Nat, Imp(Seq(k, Sp, Lt, Sp, n),
            Seq(threshold, Sp, Lt, Sp, Call("min", rk)))));
        var positive = Par(All(i, indices, Seq(D(0), Sp, Lt, Sp, Call("scaledIterate", a, p, n, i))));
        var sum = Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, indices)), Call("scaledIterate", a, p, n, i));
        var exit = And(Seq(D(0), Sp, Lt, Sp, Call("min", rn)),
            Seq(Call("min", rn), Sp, Le, Sp, threshold));
        var gap = Equal(Call("supportGap", a, p), Div(Call("supportGap", a, rn), Pow(Pow(b, D(2)), n)));
        var witness = Seq(Exists, Sp, n, Colon, Sp, Nat, Comma, Sp,
            And(Seq(D(0), Sp, Lt, Sp, n), And(before, And(positive, And(Equal(sum, D(1)), And(exit, gap))))));
        return Disp(Context(Imp(And(Seq(threshold, Sp, Lt, Sp, Call("min", p)),
            Seq(p, Sp, Neq, Sp, UniformLaw(a))), witness)));
    }

    private static Formula GlobalFormula()
    {
        var a = V("a"); var p = V("p"); var b = Pow(D(2), a);
        var coefficient = Par(Seq(b, Sp, Par(Seq(a, Sp, Plus, Sp, D(2))),
            Sp, Plus, Sp, D(2), Sp, Pow(b, D(2))));
        return Disp(Context(Seq(coefficient, Sp, Call("min", p), Sp, Minus, Sp, D(2), Sp,
            Par(Seq(b, Sp, Minus, Sp, D(1))), Sp, Le, Sp, Call("L", p)), true));
    }

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
