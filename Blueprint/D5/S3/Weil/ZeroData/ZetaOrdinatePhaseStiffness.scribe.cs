using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ZetaOrdinatePhaseStiffnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete positive zeta ordinate phase.",
        H("The complete positive zeta ordinate phase"),
        Blocks(Describe.Lean(
            DescribeId.Create("zetaordinatephasestiffness"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ZetaOrdinatePhaseStiffness.actual_zeta_phase_stiffness"),
            H("The complete positive zeta ordinate phase"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Index all distinct nontrivial complex zeta zeros rho with 0<Re(rho)<1 and "
                    + "Im(rho)>0. Write gamma(rho)=Im(rho) and m(rho) for the analytic zero "
                    + "order. Different complex zeros with equal ordinates remain separate "
                    + "indices and retain every analytic multiplicity.")),
                Paragraph(Text("Define a(rho)=m(rho)/(gamma(rho)*(1/4+gamma(rho)^2)), delta(t)=sum of "
                    + "2*a(rho)*(1-cos(gamma(rho)*t)), and v(t)=sum of "
                    + "2*a(rho)*gamma(rho)*sin(gamma(rho)*t). Both a and a*gamma are summable. "
                    + "For every real t, delta has derivative v(t), and v is continuous.")),
                Paragraph(Text("There exist real L>=2 and B>=0 such that whenever 0<abs(t) and "
                    + "L*abs(t)<=1, "
                    + "abs(delta(t)-t^2*log(1/abs(t))^2/(4*pi))<=t^2*B*(log(1/abs(t))+1), and "
                    + "abs(v(t)-t*log(1/abs(t))^2/(2*pi))<=abs(t)*B*(log(1/abs(t))+1).")),
                Paragraph(Text("The unconditional dyadic Riemann-von Mangoldt count yields a cumulative "
                    + "count error of order Y at every sufficiently large real height. A unit "
                    + "shift converts the closed upper cutoff to a strict upper cutoff within "
                    + "the same error order. The finitely many positive ordinates at or below the "
                    + "fixed high cutoff are restored with quadratic cost and linear slope "
                    + "bounds.")),
                Paragraph(Text("This is an unconditional model defined from positive ordinates. "
                    + "Identifying it with a Robin spectral expression involving the real parts "
                    + "of the zeros requires the corresponding Riemann hypothesis "
                    + "interpretation. The result does not assert a sign for a Robin remainder "
                    + "or any conclusion about a second derivative at zero."))),
            DescribeRole.Theorem))));
}
