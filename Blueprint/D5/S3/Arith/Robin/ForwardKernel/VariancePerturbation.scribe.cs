using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class VariancePerturbationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/VariancePerturbation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniformly negligible cumulative variance perturbations preserve the common-band asymptotic.",
        H("Stability of cumulative variance"),
        Blocks(
            Paragraph(Text(
                "For a real function G, write D_G(x,u)=G(x+u)-G(x) and "
                + "V_G(Y,u)=integral from 1 to Y of D_G(x,u)^2. The functions E and F "
                + "are Borel measurable and bounded on every compact interval. "
                + "These assumptions ensure square integrability of their increments. "
                + "The perturbation F is arbitrary and need not be a sum of spikes.")),
            Describe.Lean(
                DescribeId.Create("cumulative-variance-affine-error"),
                DeclarationHandle.Create(Prefix + "cumulativeVariance_affine_error"),
                H("The finite-scale affine error"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every Y>=1 and real u,t, the absolute difference between "
                    + "V_(E+tF)(Y,u) and V_E(Y,u) is at most "
                    + "2*abs(t)*sqrt(V_E(Y,u)*V_F(Y,u))+t^2*V_F(Y,u). "
                    + "Apply the reverse triangle inequality to the two increment functions "
                    + "in L2[1,Y]. Their difference is t*D_F, whose norm is "
                    + "abs(t)*sqrt(V_F). Factoring the difference of the squared norms "
                    + "gives the estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("band-asymptotic-affine"),
                DeclarationHandle.Create(Prefix + "band_asymptotic_affine"),
                H("Uniform band stability"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix 0<alpha<beta<1. Suppose V_E(Y,u)/(Y*u*log(Y/u)) tends "
                        + "uniformly to one for Y^alpha<=u<=Y^beta, while the corresponding "
                        + "ratio for F tends uniformly to zero. Then for every fixed real t, "
                        + "E+tF has the same band asymptotic. In particular t=1 and t=-1 "
                        + "give both signs of the perturbation.")),
                    Paragraph(Text(
                        "Put M=Y*u*log(Y/u), e=abs(V_E/M-1), and n=V_F/M. "
                        + "The normalized affine error is at most "
                        + "e+2*abs(t)*sqrt((V_E/M)*n)+t^2*n. Thus the original error e "
                        + "is retained with its own convergence rate. Eventually V_E/M<=2; "
                        + "if n<=delta, the additional error is at most "
                        + "2*abs(t)*sqrt(2*delta)+t^2*delta, which tends to zero with delta. "
                        + "The estimates hold simultaneously for every length in the band. "
                        + "This stability theorem supplies the variance assertion in "
                        + "CommonBandSharpness.common_band_near_optimality."))),
                DescribeRole.Theorem))));
}
