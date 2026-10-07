using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ActualFactorialRobinDyadicDerivativeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original complete factorial Robin integral has an exact low and high decomposition, and its actual dyadic growth weight has a genuine derivative with a signed error and a uniform logarithmic-ratio bound.",
        H("The Actual Robin Dyadic Growth Weight and Its Complete Derivative"),
        Blocks(
            Paragraph(Text(
                "P_x(s) is the physical integral over t>x of "
                + "eta(t/s)*weight(t), where eta and the Robin weight "
                + "are the actual functions from their existing owners. "
                + "The dyadic growth weight is exactly "
                + "b_x(s)=s*(P_x(s)-P_x(2*s)); all high-domain "
                + "factorial sources and both dyadic values remain present.")),
            Describe.Lean(
                DescribeId.Create("actual-factorial-robin-dyadic-derivative"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/ActualFactorialRobinDyadicDerivative.result"),
                H("The physical decomposition and the same-object dyadic derivative"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every 1<x<=s, the actual physical integrand "
                        + "is integrable on the complete interval t>x. "
                        + "Write ell=log(x), r=log(s), and "
                        + "F_ell(r)=r*log(r)+(1/ell-log(ell)-1)*r "
                        + "+(1/ell+ell-1)-1/r. The exact identity is "
                        + "s*P_x(s)=F_ell(r)+E(r), with E the existing "
                        + "actual complete signed high integral. At s=x the "
                        + "low interval is empty; this boundary is part of "
                        + "the public complete decomposition.")),
                    Paragraph(Text(
                        "The low part directly consumes the original "
                        + "QuotientIntegralBudget.residual_at_most_one "
                        + "to identify eta(t/s) when x<=t<=s. The proof "
                        + "pays low integrability and evaluates the three "
                        + "ordinary logarithmic integrals. The high part "
                        + "uses the real scaling change of variables t=s*y, "
                        + "pays integrability of the actual physical integrand "
                        + "on t>s, and retains the entire y>1 integral.")),
                    Paragraph(Text(
                        "For the strict derivative domain 1<x<s, the theorem "
                        + "gives HasDerivAt b_x bprime_x(s) s. "
                        + "Its exact derivative is "
                        + "s*bprime_x(s)=S_ell(r)+Eprime(r)-(1/2)*Eprime(r+L), "
                        + "where L=log(2) and "
                        + "S_ell(r)=(1/2)*log(r/ell)+1/(2*ell) "
                        + "-(1/2)*log(1+L/r)+1/r^2-1/(2*(r+L)^2). "
                        + "The one-half factor retains the actual "
                        + "normalization of P_x(2*s).")),
                    Paragraph(Text(
                        "The signed high error has complete budget "
                        + "abs(s*bprime_x(s)-S_ell(r))<=3/r^2+6/r^3. "
                        + "The actual Eprime values remain signed; their "
                        + "absolute envelopes are consumed only to bound "
                        + "this complete error. The derivative is obtained "
                        + "from an exact decomposition on a neighborhood "
                        + "and the proved complete integral derivative, "
                        + "rather than differentiation of a pointwise "
                        + "asymptotic error bound.")),
                    Paragraph(Text(
                        "When ell>=1, the same theorem supplies "
                        + "abs(s*bprime_x(s))<=(1/2)*log(r/ell)+21/(2*ell). "
                        + "Its quantifiers retain both x and s. "
                        + "At fixed x this pays growth of order "
                        + "loglog(s)/s in the derivative; the statement "
                        + "also retains the ratio of the two logarithmic scales.")),
                    Paragraph(Text(
                        "This is an analytic theorem about the original "
                        + "complete Robin kernel. The actual odd harmonic "
                        + "decay rate, complete natural-cutoff Mobius tail, "
                        + "its signed anchor and the common critical "
                        + "compensation require their additional proofs. "
                        + "No final Robin inequality or RH conclusion "
                        + "is asserted."))),
                DescribeRole.Theorem))));
}
