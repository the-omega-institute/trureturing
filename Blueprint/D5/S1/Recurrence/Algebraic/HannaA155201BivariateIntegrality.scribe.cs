using static StrataLint.Scribe.DefinitionDsl;

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
            Node("result", "Full bivariate integrality", "Fix n,j with j<=n and put M=n+1. The continuous evaluation ring homomorphism X=T^M,Y=T commutes with the formal exponential. Its logarithm equals logSum of weightedGhost with a=n; the coefficient proof explicitly matches coeff(N-r,f(r))/r with the weighted diagonal sum. For a prime p and positive r, the unit case p not dividing r is automatic. Otherwise write r=p*q and q=p^s*t with s=v_p(q). The polynomial Frobenius congruence gives p^(s+1) dividing the difference of the two weighted ghosts, since their monomial factors agree. Thus the original series-valued exp_logSum_integral_of_divisibility theorem gives an integral diagonal exponential. Coefficient isolation gives the required original coefficient. For j>n it is zero by the support bound. The n=0 boundary is included. These are formal, all-degree statements over Q[Y][[X]] for every signed integer m.", DescribeRole.Theorem)))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("hanna-a155201-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
