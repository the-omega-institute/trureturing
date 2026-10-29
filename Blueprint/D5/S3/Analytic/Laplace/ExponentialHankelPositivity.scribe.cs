using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class ExponentialHankelPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/ExponentialHankelPositivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial squares in the exponential coordinate detect positivity of an actual continuous signed L1 density.",
        H("Exponential Hankel positivity on an open half-line"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-exponential-hankel-matrix"),
                DeclarationHandle.Create(Prefix + "exponentialHankel"),
                H("Actual exponential moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a real cutoff U and a real density g, put h(k) = integral over u>U of "
                    + "g(u) exp(-k(u-U)) du, with k a natural number including zero. "
                    + "The matrix H(U,g,N) has rows and columns indexed by Fin(N+1), and entry "
                    + "h(i+j). Its entries are integrals of the supplied signed source."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("all-depth-positivity-detection"),
                DeclarationHandle.Create(Prefix + "exponential_hankel_positivity"),
                H("All depths detect pointwise positivity"),
                StatementSource.FromAuthor(DetectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real U and g:Real->Real continuous and integrable on (U,infinity), "
                        + "every moment integrand is integrable. For every natural N and every "
                        + "real coefficient vector c:Fin(N+1)->Real, let p(c,t) = sum over i of c(i)t^i. "
                        + "The function v(U,g,N,c)(u) = g(u)p(c,exp(-(u-U)))^2 is integrable and "
                        + "c^T H(U,g,N)c equals its integral. In the formula, w(U,g,k)(u) denotes "
                        + "g(u)exp(-k(u-U)), Q is this actual matrix quadratic form, and Integral "
                        + "integrates on (U,infinity) with Lebesgue measure. Coeff(N) denotes "
                        + "the entire real space Fin(N+1)->Real.")),
                    Paragraph(Text(
                        "The density is pointwise nonnegative throughout the open half-line if "
                        + "and only if H(U,g,N) is positive semidefinite for every natural N. "
                        + "No value or continuity is required at U or at infinity. L1 alone "
                        + "controls the bounded exponential weights and every polynomial square.")),
                    Paragraph(Text(
                        "For the converse, a negative interior value gives a neighborhood in "
                        + "the coordinate t=exp(-(u-U)) where the density is negative. A continuous "
                        + "triangular hat centered there vanishes outside that neighborhood. "
                        + "Weierstrass approximation on [0,1] and dominated convergence extend "
                        + "polynomial-square positivity to the hat square. Its weighted integral "
                        + "is nonpositive, hence zero; continuity on the open half-line then "
                        + "contradicts its nonzero value at the chosen point. Only the hat "
                        + "is approximated on the closed interval. The density need not extend "
                        + "to either compactification endpoint. This is a classical "
                        + "polynomial-density positivity mechanism; no priority claim is made.")),
                    Paragraph(Text(
                        "For an exponential upper cap, fix b>0 and a continuous integrable f on "
                        + "(U,infinity), and set g(u)=C exp(-bu)-f(u). The exponential term is "
                        + "integrable. Its kth moment is C exp(-bU)/(b+k), so the Hankel entry "
                        + "is C exp(-bU)/(b+i+j) minus the corresponding exponential moment of f. "
                        + "For each fixed C>=0, the theorem equates positivity of all these "
                        + "matrices with f(u)<=C exp(-bu) for every u>U. Consequently an "
                        + "existential cap must have order exists C>=0, forall N. The SAME C "
                        + "must work at every depth. The order forall N, exists C does not "
                        + "supply a common cap; this theorem does not assert fixed-depth "
                        + "cap feasibility or an effective witness depth.")),
                    Paragraph(Text(
                        "The analytic equivalence establishes no cap existence and makes no "
                        + "assertion about zeta zeros. A zero-exclusion application additionally "
                        + "needs an independently established actual-tail supplier. A supplier "
                        + "valid for 0<b<1/2 gives only its corresponding strip Re(rho)>1-b; "
                        + "it supplies neither the b=1/2 endpoint nor an RH converse."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i != 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, x, Sp, InMacro, Sp, type, Comma, Sp, body);

    private static Formula DetectionFormula()
    {
        Formula U = F.Id("U"), g = F.Id("g"), u = F.Id("u");
        Formula k = F.Id("k"), N = F.Id("N"), c = F.Id("c");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula ray = Call("Ioi", U);
        Formula v = Call("v", U, g, N, c);
        Formula Hm = Call("H", U, g, N);
        Formula moments = All(k, nat,
            Call("IntegrableOn", Call("w", U, g, k), ray));
        Formula quadratic = All(N, nat, All(c, Call("Coeff", N), Seq(
            Call("IntegrableOn", v, ray), Sp, Land, Sp,
            Call("Q", Hm, c), Sp, Eq, Sp, Call("Integral", v, ray))));
        Formula positivity = Seq(
            Open, All(u, ray, Seq(D(0), Sp, Leq, Sp, Call("g", u))), Close,
            Sp, Leftrightarrow, Sp,
            Open, All(N, nat, Call("PosSemidef", Hm)), Close);
        return Disp(All(U, real, All(g, Seq(real, Sp, To, Sp, real), Seq(
            Open, Call("ContinuousOn", g, ray), Sp, Land, Sp,
            Call("IntegrableOn", g, ray), Close, Sp, Rightarrow, Sp,
            Open, moments, Close, Sp, Land, Sp,
            Open, quadratic, Close, Sp, Land, Sp,
            Open, positivity, Close))));
    }
}
