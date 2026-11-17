using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA155201BivariateIntegralityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA155201BivariateIntegrality.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/hanna2009a155201");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer coefficients of Hanna's independent-variable formal exponential.",
        H("Hanna A155201 Bivariate Integrality"), Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS A155201 comment states: More generally, it appears that for m integer, exp( Sum_{n>=1} (m^n + y)^n * x^n/n ) is a power series in x and y with integer coefficients.")),
            Node("ghost", "Integer polynomial ghosts", "For every signed integer m and natural k, ghost m k is (C(m^k)+Y)^k in Z[Y]. The polynomial variable is independent of the outer formal series variable.", DescribeRole.Definition),
            Node("logarithmicInput", "The literal formal logarithm", "Its degree-k coefficient is (m^k+Y)^k/k in Q[Y]. Rational division makes the degree-zero coefficient zero. This is the formal sum over positive k, with no analytic convergence hypothesis.", DescribeRole.Definition),
            Node("exponentialSum", "The bivariate exponential", "Substitute the zero-constant logarithmic input into PowerSeries.exp over Q[Y]. The resulting element belongs to Q[Y][[X]] and retains both independent variables.", DescribeRole.Definition),
            Node("claim", "All signed parameters and coefficient indices", "For every integer m and natural n,j, the coefficient of X^n Y^j has an integer representative. No coefficient-integrality premise, positivity condition, scalar specialization of Y or degree cutoff occurs.", DescribeRole.Definition),
            Node("ghost_prime_power", "Polynomial Frobenius congruences", "For every prime p and natural s,t, p^(s+1) divides ghost(m,p*(p^s*t))-expand(p,ghost(m,p^s*t)) in Z[Y]. Reduction modulo p uses Fermat and the characteristic-p binomial formula. The existing power-divisibility lifting theorem raises the modulus, and taking the t-th power preserves divisibility.", DescribeRole.Theorem),
            Node("exponential_coefficient_support", "The triangular support bound", "The coefficient of Y^j in the degree-n exponential coefficient vanishes when n<j. Each logarithmic row has polynomial degree at most its outer degree, this bound is preserved under multiplication, and each exponential coefficient is a finite sum of powers.", DescribeRole.Theorem),
            Node("kronecker", "Positive-weight coefficient specialization", "The degree-N coefficient is the finite sum over outer degrees a at most N of the coefficient of Y^(N-M*a), restricted to M*a<=N. For positive M this is the ring specialization X=T^M,Y=T.", DescribeRole.Definition),
            Node("kronecker_extract", "Isolation of every triangular coefficient", "For j<=n, the coefficient of T^((n+1)*n+j) after X=T^(n+1),Y=T equals the original X^n Y^j coefficient. Smaller outer degrees require a polynomial degree beyond their support; larger outer degrees already have excessive T degree.", DescribeRole.Theorem),
            Node("weightedGhost", "Shifted series-valued Dwork weights", "The weight is T^(a*r)*(m^r+T)^r in Z[[T]]. The existing logSum inserts an additional T^r, so its total weight is T^((a+1)*r). This shift is essential for agreement with positive-weight specialization.", DescribeRole.Definition),
            Node("result", "Full bivariate integrality", "Fix n,j with j<=n and put M=n+1. The continuous evaluation ring homomorphism X=T^M,Y=T commutes with the formal exponential. Its logarithm equals logSum of weightedGhost with a=n; the coefficient proof explicitly matches coeff(N-r,f(r))/r with the weighted diagonal sum. For a prime p and positive r, the unit case p not dividing r is automatic. Otherwise write r=p*q and q=p^s*t with s=v_p(q). The polynomial Frobenius congruence gives p^(s+1) dividing the difference of the two weighted ghosts, since their monomial factors agree. Thus the original series-valued exp_logSum_integral_of_divisibility theorem gives an integral diagonal exponential. Coefficient isolation gives the required original coefficient. For j>n it is zero by the support bound. The n=0 boundary is included. These are formal, all-degree statements over Q[Y][[X]] for every signed integer m.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hanna-a155201-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(Statement(name))),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string n) => F.Id(n);
    private static Formula Call(string n, params Formula[] a)
    {
        var parts = n.Split('.');
        Formula head = V(parts[0]);
        for (int i=1; i<parts.Length; i++) head=Seq(head,Dot,V(parts[i]));
        return new Formula.Apply(Seq(Operatorname, Grp(head)), [.. a]);
    }
    private static Formula Ty(string n) => Seq(Mathbb, Grp(V(n)));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Rel(Formula a, FormulaRelationOperator r, Formula b) => new Formula.Relation(a,r,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula All(string n, string t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, Ty(t), Comma, Sp, b);
    private static Formula Ex(string n, string t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, Ty(t), Comma, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(a, Sp, Implies, Sp, b);
    private static Formula Row(Formula n) => Call("PowerSeries.coeff", n, Call("exponentialSum", V("m")));
    private static Formula Co(Formula n, Formula j) => Call("Polynomial.coeff", Row(n),j);
    private static Formula Body() => All("m","Z",All("n","N",All("j","N",Ex("z","Z",
        Eq(Co(V("n"),V("j")), Call("Int.cast",V("z")))))));
    private static Formula Statement(string name)
    {
        var m=V("m"); var n=V("n"); var j=V("j"); var k=V("k"); var r=V("r");
        var p=V("p"); var s=V("s"); var t=V("t"); var a=V("a"); var N=V("N"); var M=V("M");
        var ghost=Pow(Add(Call("Polynomial.C",Pow(m,k)),V("Y")),k);
        return name switch {
            "ghost" => All("m","Z",All("k","N",Eq(Call("ghost",m,k),ghost))),
            "logarithmicInput" => All("m","Z",All("k","N",Eq(
                Call("PowerSeries.coeff",k,Call("logarithmicInput",m)),
                Mul(new Formula.Fraction(D(1),k),ghost)))),
            "exponentialSum" => All("m","Z",Eq(Call("exponentialSum",m),Call("exp",Call("logarithmicInput",m)))),
            "claim" => Seq(Call("claim"),Sp,Iff,Sp,Body()),
            "result" => Body(),
            "ghost_prime_power" => All("m","Z",All("p","N",All("s","N",All("t","N",Imp(
                Call("Nat.Prime",p),Rel(Pow(p,Add(s,D(1))),FormulaRelationOperator.Divides,
                Sub(Call("ghost",m,Mul(p,Mul(Pow(p,s),t))),
                    Call("Polynomial.expand",p,Call("ghost",m,Mul(Pow(p,s),t)))))))))),
            "exponential_coefficient_support" => All("m","Z",All("n","N",All("j","N",Imp(
                Rel(n,FormulaRelationOperator.LessThan,j),Eq(Co(n,j),D(0)))))),
            "kronecker_extract" => All("m","Z",All("n","N",All("j","N",Imp(
                Rel(j,FormulaRelationOperator.LessThanOrEqual,n),Eq(
                Call("PowerSeries.coeff",Add(Mul(Add(n,D(1)),n),j),
                    Call("kronecker",Add(n,D(1)),Call("exponentialSum",m))),Co(n,j)))))),
            "weightedGhost" => All("a","N",All("m","Z",All("r","N",Eq(Call("weightedGhost",a,m,r),
                Mul(Pow(Add(Pow(m,r),V("T")),r),Pow(V("T"),Mul(a,r))))))),
            "kronecker" => All("M","N",All("N","N",Eq(Call("PowerSeries.coeff",N,Call("kronecker",M,V("f"))),
                Call("Finset.sum",Call("Finset.range",Add(N,D(1))),
                    Seq(V("a"),Sp,Mapsto,Sp,V("if"),Rel(Mul(M,a),FormulaRelationOperator.LessThanOrEqual,N),
                    V("then"),Call("Polynomial.coeff",Call("PowerSeries.coeff",a,V("f")),Sub(N,Mul(M,a))),V("else"),D(0)))))),
            _ => throw new System.InvalidOperationException(name)
        };
    }
}
