using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class FiniteIntegerEulerCancellationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite integer linear polynomial has signed Euler cancellation to any total degree.",
        H("Finite integer Euler cancellation"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-integer-euler-cancellation"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/EulerGerm/FiniteIntegerEulerCancellation.finite_integer_euler_cancellation"),
            H("Algebraic construction and uniform analytic evaluation"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a finite type J and N>=0, E(J,N) consists of all functions "
                    + "u:J->N with 1<=deg(u)<=N, where deg(u)=sum_j u(j). "
                    + "The coefficients a:J->Z have arbitrary signs. Write Q=1+sum_j a(j)X(j), "
                    + "U=product_u (1-X^u)^max(c(u),0), V=product_u (1-X^u)^max(-c(u),0), "
                    + "and Hpoly(a,N,c)=Q*U-V. All polynomial powers are natural powers. "
                    + "In the formula D(a,N,c) is the finite data with linear coefficients a, "
                    + "correction modes u in E(J,N), powers c(u), tail indices support(Hpoly(a,N,c)), "
                    + "tail modes t and tail coefficients coeff(Hpoly(a,N,c),t). "
                    + "L(a,N,c,u) is coeff(Hpoly(a,N,c),u).")),
                Paragraph(Text(
                    "The construction uses the variable ideal I in Z[X(j)]. Its d-th power "
                    + "consists exactly of polynomials whose coefficients below degree d vanish. "
                    + "Suppose Hpoly=QU-V belongs to I^d and V has constant coefficient one. "
                    + "Let r(u)=coeff(Hpoly,u) for each degree-d mode in support(Hpoly). Multiply U "
                    + "by A=product_u(1-X^u)^max(r(u),0), and V by "
                    + "B=product_u(1-X^u)^max(-r(u),0). In the quotient by I^(d+1), "
                    + "the degree-d monomials have pairwise zero products since d>=1. "
                    + "Polynomial.eval_add_of_sq_eq_zero applied to p=X^k, x=1 and y=-x "
                    + "gives (1-x)^k=1-k*x whenever x*x=0, including k=0. "
                    + "Thus A-B=-sum_u r(u)X^u in this quotient. The exact identity "
                    + "QUA-VB=Hpoly*A+V(A-B) removes the complete degree-d homogeneous component. "
                    + "The new error belongs to I^(d+1). Different degrees have disjoint modes.")),
                Paragraph(Text(
                    "Starting with U=V=1 and Q-1 in I, finite induction constructs the "
                    + "exponents through degree N. Unused modes are filled with zero. "
                    + "The finite-support and ordinary-function index presentations are "
                    + "transported by Finsupp.equivFunOnFinite and preserve total degree. "
                    + "Every actual tail index has degree at least N+1, since its coefficient "
                    + "is nonzero. Expanding the finite polynomial support and applying "
                    + "eval2 gives Certificate(D) for every complex vector, including "
                    + "zeros of correcting binomials. No division is used in this identity.")),
                Paragraph(Text(
                    "Certificate(D) means (1+sum_j a(j)z(j))U(z)=V(z)+P(z) for all complex z, "
                    + "where P is the finite tail sum. Let H(e)={s:Re(s)>e}, "
                    + "z(j)=exp(-b(j)s log(p)), and K(D,b,R,p,s) be "
                    + "(1+sum_j a(j)z(j)+R(p,s)) product_u(1-z^u)^c(u), using integer powers. "
                    + "Analytic(f,H) means AnalyticOnNhd over C. The existing "
                    + "evaluated_certificate_uniform theorem applied to the constructed D "
                    + "gives the displayed analytic conclusion. The exponent choice precedes "
                    + "b,m,e,A and the entire family R; C precedes R. Repeated and dependent "
                    + "weights are allowed and equality is allowed in the cutoff.")),
                Paragraph(Text(
                    "The result also allows empty J. At N=0 the correction set is empty "
                    + "and Hpoly=Q-1; Hpoly need not be zero. For Q=1+X and N=1, c(X)=1 "
                    + "gives Hpoly=-X^2. This is a finite algebraic consequence of classical "
                    + "integer Euler extraction, rather than a claim of new mathematics. "
                    + "Delabarre, Extension of Estermann's theorem to Euler products associated to a multivariate polynomial, "
                    + "BSMF 141 (2013), 225-265, DOI 10.24033/bsmf.2647, section 1.1 "
                    + "and section 2.2, Lemma 2, equations (5)-(6), Remark 4, printed pages "
                    + "233-235, gives an integral expansion Q=product(1-Y^u)^gamma(u), "
                    + "with c=-gamma. For S=sum_j |a(j)|>0, this infinite product converges "
                    + "absolutely when every |Y(j)|<1/S; the case S=0 is trivial since Q=1. "
                    + "The finite cleared polynomial identity holds for every complex vector. "
                    + "The finite cleared polynomial assertion is proved here; "
                    + "it is not the literal statement of that paper. The primary source is "
                    + "https://www.numdam.org/item/BSMF_2013__141_2_225_0.pdf. "
                    + "No infinite prime product, nonvanishing, zero localization, or O-5 "
                    + "conclusion is asserted."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula j = F.Id("J"), a = F.Id("a"), n = F.Id("N"), kappa = F.Id("c");
        Formula d = Call("D", a, n, kappa), b = F.Id("b");
        Formula m = F.Id("m"), e = F.Id("e"), bound = F.Id("A");
        Formula c = F.Id("C"), r = F.Id("R"), p = F.Id("p"), s = F.Id("s");
        Formula ri = F.Id("i"), rt = F.Id("t"), rj = F.Id("j"), u = F.Id("u");
        Formula h = Call("H", e);
        Formula invSquare = new Formula.Fraction(F.D(1), new Formula.Power(p, F.D(2)));
        Formula k = Call("K", d, b, r, p, s);
        return F.Disp(new Formula.Aligned([
            Seq(F.Forall, F.Sp, j, F.Colon, Call("Type"), F.Comma,
                F.OpenBracket, Call("Fintype", j), F.CloseBracket, F.Comma,
                F.Sp, F.Forall, F.Sp, a, F.Colon, j, F.Rightarrow, Number("Z"), F.Comma,
                F.Sp, F.Forall, F.Sp, n, F.InMacro, F.Sp, Number("N"), F.Comma),
            Seq(F.Exists, F.Sp, kappa, F.Colon, Call("E", j, n), F.Rightarrow, Number("Z"), F.Comma),
            Seq(F.Open, F.Forall, F.Sp, u, F.Colon, j, F.Rightarrow, Number("N"), F.Comma,
                F.Sp, Call("deg", u), F.Leq, F.Sp, n, F.Sp, F.Implies, F.Sp,
                Call("L", a, n, kappa, u), F.Eq, F.D(0), F.Close, F.Sp, F.Land),
            Seq(Call("Certificate", d), F.Sp, F.Land),
            Seq(F.Open, F.Forall, F.Sp, ri, F.InMacro, F.Sp, Call("E", j, n), F.Comma,
                F.Sp, F.D(1), F.Leq, F.Sp, Call("deg", Call("mode", d, ri)), F.Sp, F.Land,
                Call("deg", Call("mode", d, ri)), F.Leq, F.Sp, n, F.Close, F.Sp, F.Land),
            Seq(F.Open, F.Forall, F.Sp, rt, F.InMacro, F.Sp, Call("support", Call("Hpoly", a, n, kappa)),
                F.Comma, F.Sp, n, F.Plus, F.D(1), F.Leq, F.Sp,
                Call("deg", Call("tailMode", d, rt)), F.Close, F.Sp, F.Land),
            Seq(F.Forall, F.Sp, b, F.Colon, j, F.Rightarrow, Number("R"), F.Comma,
                F.Sp, F.Forall, F.Sp, m, F.Comma, e, F.Comma, bound,
                F.InMacro, F.Sp, Number("R"), F.Comma),
            Seq(F.D(0), F.Lt, m, F.Sp, F.Land, F.Sp,
                F.Open, F.Forall, F.Sp, rj, F.InMacro, F.Sp, j, F.Comma,
                F.Sp, m, F.Leq, F.Sp, Call("b", rj), F.Close,
                F.Sp, F.Land, F.Sp, F.D(0), F.Lt, e,
                F.Sp, F.Land, F.Sp, F.D(0), F.Leq, F.Sp, bound,
                F.Sp, F.Land, F.Sp, F.D(2), F.Leq, F.Sp,
                F.Open, n, F.Plus, F.D(1), F.Close, e, m,
                F.Sp, F.Implies),
            Seq(F.Exists, F.Sp, c, F.InMacro, F.Sp, Number("R"), F.Comma,
                F.Sp, F.D(0), F.Leq, F.Sp, c, F.Sp, F.Land,
                F.Sp, F.Forall, F.Sp, r, F.Colon,
                Call("Primes"), F.Rightarrow, Number("C"), F.Rightarrow, Number("C"), F.Comma),
            Seq(F.Open, F.Forall, F.Sp, p, F.InMacro, F.Sp, Call("Primes"), F.Comma,
                F.Sp, Call("Analytic", Call("R", p), h), F.Close,
                F.Sp, F.Land, F.Sp,
                F.Open, F.Forall, F.Sp, p, F.InMacro, F.Sp, Call("Primes"), F.Comma,
                F.Sp, F.Forall, F.Sp, s, F.InMacro, F.Sp, h, F.Comma,
                F.Sp, Call("norm", Call("R", p, s)), F.Leq, F.Sp, bound, invSquare, F.Close,
                F.Sp, F.Implies),
            Seq(F.Forall, F.Sp, p, F.InMacro, F.Sp, Call("Primes"), F.Comma,
                F.Sp, Call("Analytic", Call("K", d, b, r, p), h),
                F.Sp, F.Land, F.Sp,
                F.Open, F.Forall, F.Sp, s, F.InMacro, F.Sp, h, F.Comma,
                F.Sp, Call("norm", Seq(k, F.Minus, F.D(1))), F.Leq, F.Sp, c, invSquare, F.Close)
        ]));
    }

    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula Call(string name, params Formula[] xs)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int k = 0; k < xs.Length; k++)
        {
            if (k > 0) { pieces.Add(F.Comma); pieces.Add(F.Sp); }
            pieces.Add(xs[k]);
        }
        pieces.Add(F.Close);
        return Seq(pieces.ToArray());
    }
    private static Formula Number(string name) => Seq(F.Mathbb, F.Grp(F.Id(name)));
}
