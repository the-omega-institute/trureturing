using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class WeightedMangoldtRateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Mertens/WeightedMangoldtRate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An unconditional rate for the actual inclusive weighted Mangoldt error, "
            + "derived from the existing exponent-one-tenth Chebyshev estimate.",
        H("Actual weighted Mangoldt rate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-weighted-mangoldt-stretched-exponential"),
                DeclarationHandle.Create(Prefix + "E1Lambda_stretched_exponential"),
                H("Unconditional stretched-exponential decay at every large real cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exist real c>0, C>0 and X>=2 such that for every real x>=X, "
                        + "|Mertens.E₁Λ(x)+EulerGamma| <= C*exp(-c*(log x)^(1/10)). "
                        + "Here E₁Λ(x) is the original sum of Lambda(n)/n over "
                        + "0<n<=floorNat(x), minus log(x). Every prime power is present, "
                        + "including a term exactly at an integer cutoff. The conclusion has "
                        + "no RH, zero-location, integrability or supplied-rate hypothesis.")),
                    Paragraph(Text(
                        "Reuse is explicit: MediumPNT supplies c0>0, D>0 and a threshold A "
                        + "with |psi(u)-u| <= D*u*exp(-c0*(log u)^(1/10)) for all u>=A. "
                        + "Set X=max(A,2), c=c0/2 and w(u)=exp(-c*(log u)^(1/10))/u. "
                        + "The Gaussian integrability theorem with s=0, p=1/10 and b=c "
                        + "and the logarithmic substitution prove that w is integrable on u>1. "
                        + "Its real integral J is finite and nonnegative. This follows from "
                        + "absolute integrability; no positivity conclusion is inferred from a "
                        + "totalized undefined integral.")),
                    Paragraph(Text(
                        "For u>x>=X, log(u)>=log(x)>=0 and the positive real power 1/10 "
                        + "is monotone. Split the PNT exponential exactly into two factors "
                        + "of exponent -c*(log u)^(1/10). The first factor is at most "
                        + "exp(-c*(log x)^(1/10)), so the absolute Chebyshev kernel is at most "
                        + "D*exp(-c*(log x)^(1/10))*w(u). The existing "
                        + "chebyshev_error_kernel_integrable supplies absolute integrability "
                        + "of the actual kernel on u>1 and hence on u>x. Absolute integral "
                        + "domination, extraction of the constant, and monotonicity of the "
                        + "nonnegative w integral give the complete tail bound "
                        + "D*J*exp(-c*(log x)^(1/10)). The point term (psi(x)-x)/x "
                        + "has absolute value at most D times the same exponential.")),
                    Paragraph(Text(
                        "The existing complete_chebyshev_tail_identity at each real x>=2 "
                        + "gives E₁Λ(x)+EulerGamma=(psi(x)-x)/x minus the integral of "
                        + "(psi(u)-u)/u^2 over u>x. The minus-one term in that identity "
                        + "cancels exactly with x/x. The triangle inequality yields the rate "
                        + "with C=D*(1+J)>0. The finite inclusive sum and the open Lebesgue "
                        + "tail come from this exact identity; no integer-only limit, "
                        + "prime-only truncation or replacement error function is used.")),
                    Paragraph(Text(
                        "This is a quantitative strengthening of the existing E1Lambda_tendsto, "
                        + "which is reused as context and is not reproved. The analytic "
                        + "argument is a classical PNT consequence; no literature novelty "
                        + "or stronger external PNT is asserted. Substitution x=exp(t) "
                        + "identifies the later b(t)=EulerGamma-t+sum(2<=n<=exp(t),Lambda(n)/n), "
                        + "because Lambda(1)=0. A complete joint Stieltjes identity, "
                        + "the prime/continuum/boundary remainder and both frequency ranges "
                        + "are still required for the proposed kappa_D scale. This theorem "
                        + "alone establishes neither N(D)=o(D) nor the literal RH goal."))),
                DescribeRole.Theorem)),
        []));
}
