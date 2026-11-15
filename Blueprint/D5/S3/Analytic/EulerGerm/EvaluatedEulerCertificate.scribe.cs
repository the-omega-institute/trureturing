using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.EulerGerm;

internal sealed class EvaluatedEulerCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite algebraic cancellation identity controls one entire family of analytic prime remainders.",
        H("Evaluated Euler cancellation certificates"),
        Blocks(Describe.Lean(
            DescribeId.Create("evaluated-euler-certificate-uniform"),
            DeclarationHandle.Create(
                "D5/S3/Analytic/EulerGerm/EvaluatedEulerCertificate.evaluated_certificate_uniform"),
            H("Uniform analytic evaluation of a finite certificate"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The three index types J, I and T are finite and may be empty. "
                    + "The data d consist of integer linear coefficients a(j), correction "
                    + "multiindices n(i,j), signed integer powers c(i), tail multiindices "
                    + "u(t,j), and integer tail coefficients h(t). Write z^n for the product "
                    + "of z(j)^n(j) over J. Let U(z) be the product of (1-z^n(i))^max(c(i),0), "
                    + "V(z) the product of (1-z^n(i))^max(-c(i),0), and P(z) the sum of "
                    + "h(t) z^u(t). Certificate(d) means the identity "
                    + "(1+sum_j a(j)z(j)) U(z)=V(z)+P(z) for every complex vector z. "
                    + "These finite data and their identity precede all analytic choices.")),
                Paragraph(Text(
                    "In the formula, deg(n) is sum_j n(j), H(e) is the open halfplane "
                    + "Re(s)>e, and primes are natural primes. Set z(j)=exp(-b(j)s log(p)) "
                    + "and K(d,b,R,p,s)=(1+sum_j a(j)z(j)+R(p,s)) "
                    + "times the product of (1-z^n(i))^c(i), using integer powers. "
                    + "Analytic(f,H) denotes AnalyticOnNhd over the complex numbers: "
                    + "f is analytic at every point of H. Since H is open, this is the "
                    + "ordinary analytic-on-H condition.")),
                Paragraph(Text(
                    "The lower weight m is positive and satisfies m<=b(j) for every j. "
                    + "For a nonempty J it can be the minimum weight. Repeated and rationally "
                    + "dependent weights require no special cases. The order N may be zero, "
                    + "the cutoff inequality includes equality, and every positive e is allowed. "
                    + "The constant is chosen before R and is uniform in the prime and point.")),
                Paragraph(Text(
                    "For an explicit bound, put q=exp(-m e log(2)), "
                    + "B=product_i (1+q)^max(c(i),0), "
                    + "D=product_i (1-q)^max(-c(i),0), and L=sum_t |h(t)|. "
                    + "Then 0<q<1 and C=(L+A B)/D is valid. Each correcting monomial "
                    + "has norm at most q. Each tail monomial has norm at most p^(-2). "
                    + "The certificate gives K-1=(P+R U)/V, while the denominator norm "
                    + "is at least D>0. This proves the bound for the entire R family. "
                    + "Nonzero correcting binomials also justify analytic integer powers.")),
                Paragraph(Text(
                    "The remaining all-order problem is to construct, for every finite "
                    + "integer linear polynomial and N, such a certificate using only "
                    + "correction multiindices of degrees one through N and tails of "
                    + "degree at least N+1. This theorem assumes that finite algebraic "
                    + "identity; it does not construct the exponents. It asserts no "
                    + "nonvanishing of K, convergence of an infinite prime product, "
                    + "zero localization, or O-5 conclusion."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula j = F.Id("J"), i = F.Id("I"), t = F.Id("T");
        Formula d = F.Id("d"), n = F.Id("N"), b = F.Id("b");
        Formula m = F.Id("m"), e = F.Id("e"), a = F.Id("A");
        Formula c = F.Id("C"), r = F.Id("R"), p = F.Id("p"), s = F.Id("s");
        Formula ri = F.Id("i"), rt = F.Id("t"), rj = F.Id("j");
        Formula h = Call("H", e);
        Formula invSquare = new Formula.Fraction(F.D(1), new Formula.Power(p, F.D(2)));
        Formula k = Call("K", d, b, r, p, s);
        return F.Disp(new Formula.Aligned([
            Seq(F.Forall, F.Sp, j, F.Comma, i, F.Comma, t, F.Colon, F.Sp,
                Call("Type"), F.Comma, F.Sp,
                F.OpenBracket, Call("Fintype", j), F.CloseBracket,
                F.OpenBracket, Call("Fintype", i), F.CloseBracket,
                F.OpenBracket, Call("Fintype", t), F.CloseBracket, F.Comma),
            Seq(F.Forall, F.Sp, d, F.Colon, Call("Data", j, i, t), F.Comma,
                F.Sp, F.Forall, F.Sp, n, F.InMacro, F.Sp, Number("N"), F.Comma),
            Seq(Call("Certificate", d), F.Sp, F.Land, F.Sp,
                F.Open, F.Forall, F.Sp, ri, F.InMacro, F.Sp, i, F.Comma,
                F.Sp, F.D(1), F.Leq, F.Sp, Call("deg", Call("mode", d, ri)), F.Close,
                F.Sp, F.Land, F.Sp,
                F.Open, F.Forall, F.Sp, rt, F.InMacro, F.Sp, t, F.Comma,
                F.Sp, n, F.Plus, F.D(1), F.Leq, F.Sp,
                Call("deg", Call("tailMode", d, rt)), F.Close,
                F.Sp, F.Implies),
            Seq(F.Forall, F.Sp, b, F.Colon, j, F.Rightarrow, Number("R"), F.Comma,
                F.Sp, F.Forall, F.Sp, m, F.Comma, e, F.Comma, a,
                F.InMacro, F.Sp, Number("R"), F.Comma),
            Seq(F.D(0), F.Lt, m, F.Sp, F.Land, F.Sp,
                F.Open, F.Forall, F.Sp, rj, F.InMacro, F.Sp, j, F.Comma,
                F.Sp, m, F.Leq, F.Sp, Call("b", rj), F.Close,
                F.Sp, F.Land, F.Sp, F.D(0), F.Lt, e,
                F.Sp, F.Land, F.Sp, F.D(0), F.Leq, F.Sp, a,
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
                F.Sp, Call("norm", Call("R", p, s)), F.Leq, F.Sp, a, invSquare, F.Close,
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
