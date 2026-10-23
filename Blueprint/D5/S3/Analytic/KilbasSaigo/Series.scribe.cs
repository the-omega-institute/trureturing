using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KilbasSaigo;

internal sealed class SeriesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Entire real series and signed derivatives for the Kilbas-Saigo function.",
        H("Gamma ratios and differentiated series"), Blocks(
            Definition("kilbas-saigo-phi", "phi", "The affine Gamma ratio",
                "With a=1+alpha(l-m) and b=alpha m, phi(s)=Gamma(a+b s+alpha)/Gamma(a+b s)."),
            Definition("kilbas-saigo-g-coefficient", "gCoeff", "Derivative coefficients",
                "The coefficient d(k,n) is (n+k)!/n! times the coefficient c(n+k) of the defining series."),
            Definition("kilbas-saigo-g", "g", "Signed derivative series",
                "The series g(k,x) is the sum of d(k,n)(-x)^n over natural n."),
            Theorem("kilbas-saigo-base-positive", "base_pos", "Positive initial argument",
                "The assumptions alpha>0 and l>m-1/alpha imply a=1+alpha(l-m)>0."),
            Theorem("kilbas-saigo-phi-positive", "phi_pos", "Positive Gamma ratios",
                "For alpha>0, m>0, l>m-1/alpha and s>=0, phi(s)>0, since both Gamma arguments are positive."),
            Theorem("kilbas-saigo-coefficient-successor", "ksCoeff_succ", "Coefficient recurrence",
                "The product defining c(n+1) equals c(n)/phi(n+1). This identity holds for all real parameters."),
            Theorem("kilbas-saigo-coefficient-positive", "ksCoeff_pos", "Positive coefficients",
                "For alpha>0, m>0 and l>m-1/alpha, every coefficient c(n) is strictly positive."),
            Theorem("kilbas-saigo-reciprocal-beta", "inv_phi_eq_beta", "A beta integral for the reciprocal ratio",
                "For admissible parameters and s>=0, 1/phi(s) equals the integral from zero to one of r^(a+b s-1)(1-r)^(alpha-1), divided by Gamma(alpha)."),
            Theorem("kilbas-saigo-ratio-decay", "tendsto_inv_phi", "Decay of reciprocal Gamma ratios",
                "For alpha>0, m>0 and l>m-1/alpha, 1/phi(n) tends to zero as n tends to infinity. The beta density with exponent a-1 dominates all densities in the sequence; at every interior point the exponent tends to infinity."),
            Theorem("kilbas-saigo-derivative-ratio", "gCoeff_succ", "Derivative coefficient recurrence",
                "The ratio recurrence for d(k,n+1) is ((n+k+1)/(n+1))/phi(n+k+1) times d(k,n)."),
            Theorem("kilbas-saigo-derivative-step", "gCoeff_step", "The differentiated coefficient",
                "Multiplying d(k,n+1) by n+1 gives d(k+1,n)."),
            Theorem("kilbas-saigo-derivative-summable", "summable_gCoeff", "Convergence of derivative series",
                "For alpha>0, m>0 and l>m-1/alpha, each derivative coefficient series converges absolutely at every real argument. Its successive multiplier tends to zero, so a geometric majorant applies to its tail."),
            Theorem("kilbas-saigo-entire-real", "summable_kilbasSaigo", "Convergence of the defining series",
                "The defining Kilbas-Saigo series converges for every real argument under alpha>0, m>0 and l>m-1/alpha."),
            Theorem("kilbas-saigo-g-zero", "g_zero", "Initial derivative values",
                "The value g(k,0) is k! c(k), for every real parameter triple."),
            Theorem("kilbas-saigo-g-zero-positive", "g_zero_pos", "Positive initial derivatives",
                "Under alpha>0, m>0 and l>m-1/alpha, each g(k,0) is strictly positive."),
            Theorem("kilbas-saigo-g-zero-order", "kilbasSaigo_neg_eq_g0", "The original series as order zero",
                "For every real parameter triple and x, the defining function at -x is g(0,x)."),
            Theorem("kilbas-saigo-termwise-derivative", "hasDerivAt_g", "Differentiating the series",
                "For alpha>0, m>0 and l>m-1/alpha, g(k,x) has derivative -g(k+1,x) at every real x. On each bounded interval, the next derivative series supplies a summable uniform bound on monomial derivatives."),
            Theorem("kilbas-saigo-continuity", "continuous_g", "Continuity of all derivative series",
                "Each g(k,.) is continuous on the whole real line under the same parameter assumptions."))));

    private static DocumentBlock Definition(string id, string name, string title, string text) =>
        Entry(id, name, title, text, DescribeRole.Definition);
    private static DocumentBlock Theorem(string id, string name, string title, string text) =>
        Entry(id, name, title, text, DescribeRole.Theorem);
    private static DocumentBlock Entry(string id, string name, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/KilbasSaigo/Series." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
