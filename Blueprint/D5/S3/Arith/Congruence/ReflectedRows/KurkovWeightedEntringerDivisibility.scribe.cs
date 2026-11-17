using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence.ReflectedRows;

internal sealed class KurkovWeightedEntringerDivisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/ReflectedRows/KurkovWeightedEntringerDivisibility.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/kurkov2025a386381");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive divisor of a term of the modified Entringer diagonal divides all terms at the corresponding arithmetic progression of indices.",
        H("Kurkov's all-divisor conjecture for A386381"),
        Blocks(
            Node("triangle", "The literal A386363 triangle", TriangleFormula(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "The natural array has T(0,0)=1 and T(n,0)=0 for positive n. "
                + "For positive n its first value is T(n,1)=T(n-1,n-1). "
                + "For 2<=k<=n its update is T(n,k)=T(n,k-1)+(n-2)*T(n-1,n-k). "
                + "Natural subtraction in the coefficient agrees with integer subtraction in this range. "
                + "The total Lean definition also assigns auxiliary values outside the row; "
                + "the theorem uses the published triangular region. The n=0 clause has priority."),
            Node("a", "The diagonal sequence", All("n", N(), EqF(Call("a", V("n")), Call("triangle", V("n"), V("n")))), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "The sequence is exactly a(n)=T(n,n), indexed from zero. "
                + "In particular a(0)=a(1)=a(2)=1. The last update for n>=2 adds a multiple "
                + "of T(n-1,0)=0, so a(n)=T(n,n-1). Every a(n) is positive."),
            Node("result", "The complete first source conjecture", ResultFormula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The first conjunct quantifies over k,m in N and positive d in Z, and uses integer "
                + "divisibility. Int.toNat occurs only in the index k+m*d.toNat; positivity gives "
                + "(d.toNat:Z)=d. The second conjunct is the source's a(k)-divisibility consequence "
                + "over N, consumed directly in this conjunction using positivity of a(k). "
                + "There is no finite cutoff or primality restriction. k=0, m=0 and d=1 are included. "
                + "Conjecture 2 and A060818 are separate and are not asserted here.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a386381-divisor-propagation"), ResolutionKind.Proved)),
            Paragraph(Text(
                "For a rational polynomial f, S_N(f) is anchored at 1 with value zero and has "
                + "backward difference f(N-X). It is constructed by applying the earlier frozen "
                + "IntegerNewton.int_newton_of_fwdDiff_iter_eq_zero to the integer restriction of "
                + "f(N-X), then replacing each binomial term by its backward antiderivative "
                + "binom(X+1,j+1)-binom(2,j+1). Mathlib supplies the difference-vanishing bound, "
                + "Pascal identity and Pochhammer polynomials.")),
            Paragraph(Text(
                "Write Q(N,0)=1 and Q(N,j+1)=S_N(Q(N-1,j)). These polynomials have degree at most j "
                + "and take integer values at every integer. Applying the same Newton reconstruction "
                + "at order j+1 gives an integral polynomial for j!*Q(N,j), since i! divides j! "
                + "for every i<=j. The implemented P(r), corresponding to source row n=r+2, is the "
                + "sum over 0<=j<=r of r falling j times a(r+1-j) times Q(r+2,j). "
                + "The identity r falling j=j!*choose(r,j) proves that P(r) has integer coefficients. "
                + "This cancellation takes place over Q before reducing modulo d. "
                + "Integer-valuedness by itself is never used as a period-d claim.")),
            Paragraph(Text(
                "The row polynomial has value a(r+1) at 1 and backward difference "
                + "r*P(r-1)(r+2-X) when r is positive. Induction identifies its evaluation "
                + "with T(r+2,k) only for 1<=k<=r+1. Its evaluation at r+1 is a(r+2). "
                + "No polynomial equality with the whole source row outside this interval is assumed.")),
            Paragraph(Text(
                "For a positive modulus d, evaluate these integral polynomials in ZMod d. "
                + "Their integer argument has period d. Induction on r proves P(r+d)(x)=a(d+1)*P(r)(x) "
                + "pointwise at every integer x. At r=0 the backward differences vanish modulo d; "
                + "the anchor is a(d+1). At the inductive step, the previous row relation and argument "
                + "periodicity give both the anchor and the backward differences. Two-sided integer "
                + "induction propagates equality to all arguments. The diagonal gives "
                + "a(n+d)=a(d+1)*a(n) in ZMod d for positive n,d, and induction on m gives divisor "
                + "propagation. If k=0, the hypothesis d|a(0)=1 forces d=1.")),
            Paragraph(Text(
                "The Newton ingredient is classical and reused from the repository and pinned Mathlib. "
                + "The reflected row construction and full source deduction are repository derived. "
                + "No external Lean code is transplanted. Bounded literature searches are described "
                + "in the Library note; global novelty and priority remain "
                + "ASSUMED-UNVERIFIED.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("a386381-" + name), DeclarationHandle.Create(Prefix + name), H(title),
        StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula V(string s) => F.Id(s);
    private static Formula N() => Seq(Mathbb, Grp(V("N")));
    private static Formula Z() => Seq(Mathbb, Grp(V("Z")));
    private static Formula All(string s, Formula type, Formula body) =>
        Seq(Forall, Sp, V(s), Colon, Sp, type, Comma, Sp, body);
    private static Formula Call(string s, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. args]);
    private static Formula EqF(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Divides(Formula a, Formula b) => Seq(a, Sp, Mid, Sp, b);
    private static Formula AndF(Formula a, Formula b) => Seq(Open, a, Sp, Land, Sp, b, Close);
    private static Formula Implies(Formula a, Formula b) => Seq(Open, a, Sp, Rightarrow, Sp, b, Close);

    private static Formula TriangleFormula()
    {
        var n = V("n"); var k = V("k");
        Formula T(Formula i, Formula j) => Call("triangle", i, j);
        var step = All("k", N(), Implies(Seq(D(2), Sp, Le, Sp, k, Sp, Le, Sp, n),
            EqF(T(n, k), Add(T(n, Sub(k, D(1))),
                Mul(Sub(n, D(2)), T(Sub(n, D(1)), Sub(n, k)))))));
        return AndF(EqF(T(D(0), D(0)), D(1)), All("n", N(),
            Implies(Seq(D(0), Sp, Lt, Sp, n), AndF(EqF(T(n, D(0)), D(0)),
                AndF(EqF(T(n, D(1)), T(Sub(n, D(1)), Sub(n, D(1)))), step)))));
    }

    private static Formula ResultFormula()
    {
        var k = V("k"); var m = V("m"); var d = V("d");
        var general = All("k", N(), All("m", N(), All("d", Z(),
            Implies(Seq(D(0), Sp, Lt, Sp, d), Implies(Divides(d, Call("a", k)),
                Divides(d, Call("a", Add(k, Mul(m, Call("toNat", d))))))))));
        var particular = All("k", N(), All("m", N(), Divides(Call("a", k),
            Call("a", Add(k, Mul(m, Call("a", k)))))));
        return AndF(general, particular);
    }
}
