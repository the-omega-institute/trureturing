using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class SingleSmallSourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula k = V("k"), t = V("t"), a = V("a"), i = V("i"), j = V("j"), n = V("n");
        Formula f = Call("actualSource", k, t), fa = Call("actualSource", k, t, a);
        Formula N = Call("modulus", k), C = Call("half", k), Qtr = Call("quarter", k);
        Formula assumptions = And(Le(Num(3), k), Lt(Call("abs", fa), Qtr),
            Q(Imp(Ne(i, a), Call("Large", k, t, i)), ("i", Call("Fin", k))));
        Formula w = Call("orientedPhaseSource", k, t, a, j);
        Formula odd = Eq(Call("mod", j, Num(2)), Num(1));
        Formula profile = Q(Imp(And(Le(Num(1), j), Le(j, k)),
            And(Call("ite", odd, Lt(Num(0), w), Lt(w, Num(0))),
                Eq(Mul(Num(3), w), Sub(Call("ite", odd, N, Neg(N)),
                    Pow(Num(2), Sub(j, Num(1))))))), ("j", Name("Nat")));
        Formula rigidity = Q(Imp(assumptions,
            And(Eq(Call("mod", k, Num(2)), Num(1)),
                Eq(Mul(Num(3), Call("abs", fa)), C), profile)),
            ("k", Name("Nat")), ("t", Name("Nat")), ("a", Call("Fin", k)));
        Formula start = Call("ite", Lt(Num(0), fa), a, Call("phase", a, Num(2)));
        Formula word = Call("path", start, k);
        Formula prefix = Call("sum", Call("map", f, Call("take", n, word)));
        Formula completion = Q(Imp(assumptions,
            And(Call("Perm", word, Call("finRange", k)), Call("Nodup", word),
                Eq(Call("toFinset", word), Call("univ", Call("Fin", k))),
                Call("InStrip", f, C, Num(0), word),
                Q(And(Le(Num(0), prefix), Le(prefix, C)), ("n", Name("Nat"))),
                Eq(Call("sum", Call("map", f, word)), Num(0)))),
            ("k", Name("Nat")), ("t", Name("Nat")), ("a", Call("Fin", k)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "One physical SMALL defect forces an odd native doubling period and an exact profile; its complete forward physical cycle fits the half-modulus strip.",
            H("Single SMALL rigidity and forward cyclic completion"),
            Blocks(
                Describe.Lean(DescribeId.Create("single-small-native-rigidity"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Circle/SingleSmallSource.single_small_rigidity"),
                    H("Period closure determines the amplitude and every phase"),
                    StatementSource.FromAuthor(rigidity), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("Let k>=3, N=2^k-1, C=N div 2=2^(k-1)-1, Q=2^(k-2), and f(i)=SourceWidth.actualSource(k,t,i)=centered(N,2^i*t) on the physical type Fin(k). The natural parameter t is unrestricted. Assume a is SMALL, |f(a)|<Q, and each physical i different from a is LARGE, Q<=|f(i)|. No injectivity, coprimality, or least-period assumption is supplied.")),
                        Paragraph(Text("phase(a,j) is the existing forward physical label (a.val+j) mod k. Its omitted argument is a proof of 0<k. orientedPhaseSource(k,t,a,j) abbreviates orient(decide(f(a)<0), f(phase(a,j))); ite denotes the ordinary conditional. These are display abbreviations, not new Lean definitions. The profile and its strict sign clause hold for every 1<=j<=k, including the returning endpoint.")),
                        Paragraph(Text("Orient signs so w(0)=s=|f(a)|. The SMALL step has no wrap and w(1)=2s. Since phase(a,1) is a different physical label and LARGE, s is positive. For phases 1 through k-1, centered bounds and LARGE force a sign change at each step. A simultaneous induction proves the sign alternation and 3w(j)=(N for odd j, -N for even j)+2^(j-1)*(6s-N). The physical return w(k)=s forces k odd. Writing A=2^(k-1), closure gives 3s=N+A(6s-N), while N=2A-1 and C=A-1. Cancellation of positive N yields 3s=C and 6s-N=-1.")),
                        Paragraph(Text("The sign changes belong to the native centered doubling dynamics, including its return across the physical seam. There is no upper bound on k in the statement or on the number k-1 of LARGE labels. This restricted native-source result leaves arbitrary-source Circle C3.1 open."))),
                    DescribeRole.Theorem),
                Describe.Lean(DescribeId.Create("single-small-forward-half-width-completion"),
                    DeclarationHandle.Create("D5/S3/Combinatorics/Circle/SingleSmallSource.single_small_forward_completion"),
                    H("One complete forward physical permutation at half width"),
                    StatementSource.FromAuthor(completion), AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text("The displayed word is explicit: start at a when f(a)>0, and at phase(a,2) when f(a)<0, then take all k forward physical labels. Zero at a is ruled out by rigidity. path(start,k) is the existing map of phase(start,j) over j=0,...,k-1. The theorem proves permutation equivalence with finRange(k), Nodup, exhaustive univ, InStrip at height zero and capacity C, every natural take-prefix in [0,C], and full sum zero. It preserves the whole forward LARGE cyclic order, hence also either sign's cyclic queue; there is no reversal.")),
                        Paragraph(Text("For the oriented positive source g define the unsigned height v(i)=g(i)+N when g(i)<0, and v(i)=g(i) otherwise. The rigidity profile implies s<=v(i)<=4s on every physical label, v(a)=s, and v(phase(a,2))=4s. Indeed for odd j, 3v_j=N-2^(j-1); for positive even j, 3v_j=2N-2^(j-1). The inequalities 1<=2^(j-1)<=2^(k-1), and 2<=2^(j-1) on positive even phases, give the stated range using N=6s+1 and C=3s. The strict profile signs also exclude zero on every label.")),
                        Paragraph(Text("For the original source use its unsigned height u=f+N when f<0 and u=f otherwise. If f(a)>0 then u=v, so a attains the minimum. If f(a)<0 then u=N-v, since no source value is zero, so phase(a,2) attains the minimum. In both cases 0<=u(i)-u(start)<=3s=C. SourceWidth.unsigned_step, path_range and path_sum telescope each forward prefix to this height difference. A natural take uses min(n,k), covering n=0, n=k and n>k; closure gives sum zero.")),
                        Paragraph(Text("Physical permutation is proved using finCycle(start).map_finRange_perm. Distinct labels remain distinct occurrences even when their numerical values agree, and no numerical period quotient is used. Any shorter numerical period is handled by the same physical statement rather than excluded by a premise. The package supplies this one-defect completion only: completion for two SMALL labels, the arbitrary-source exchange, and full Circle C3.1 remain open."))),
                    DescribeRole.Theorem)), []));
    }

    private static Formula V(string s) => F.Id(s);
    private static Formula Name(string s) => new Formula.NamedConstant(FormulaIdentifier.Create(s));
    private static Formula Num(long n) => new Formula.Number(n);
    private static Formula Call(string s, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula Q(Formula body, params (string Name, Formula Domain)[] vs)
    {
        for (var i = vs.Length - 1; i >= 0; --i)
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(vs[i].Name), vs[i].Domain, body);
        return body;
    }
    private static Formula And(params Formula[] a)
    {
        var body = a[^1];
        for (var i = a.Length - 2; i >= 0; --i) body = new Formula.Logic(a[i], FormulaLogicOperator.And, body);
        return body;
    }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
}
