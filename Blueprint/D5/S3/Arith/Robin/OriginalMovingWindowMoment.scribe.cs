using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalMovingWindowMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalMovingWindowMoment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit uniform error controls the continuous decaying moment of the original Robin moving-window kernel.",
        H("The Original Moving-Window Moment"),
        Blocks(
            Paragraph(Text(
                "Use lambda(x)=1/(x log(x)) and the existing weight "
                + "w(x)=(log(x)+1)/(x^2 log(x)^2). The original window has "
                + "H(t)=t^(4/5), B(t)=t+H(t) and kernel "
                + "k(t,x)=(lambda(x)-lambda(B(t)))/(w(t)*t^(11/10)) "
                + "for t<x<=B(t), and zero elsewhere. In particular k(t,t)=0 "
                + "and k(t,B(t))=0. The price is evaluated only inside the "
                + "legal window; real powers are Real.rpow.")),
            Describe.Lean(
                DescribeId.Create("original-window-moment-estimate"),
                DeclarationHandle.Create(Prefix + "original_window_moment_estimate"),
                H("A quantitative continuous moment supplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real t>=4 and beta>=0, define "
                        + "a_beta(t)=integral from t to B(t) of "
                        + "k(t,x)*(x-2)^(-beta). With "
                        + "C_beta=4+beta+2*beta*2^(beta+1), "
                        + "|a_beta(t)-t^(1/2-beta)/2| <= "
                        + "C_beta*t^(-1/5)*t^(1/2-beta)/2.")),
                    Paragraph(Text(
                        "The proof reuses ActualRobinClockCovariance.g, its "
                        + "original derivative and density-integral suppliers, "
                        + "and MellinWeightedVariation.scaleWeight_antitone. "
                        + "Their weight normalization gives "
                        + "w(B)*(B-x)<=lambda(x)-lambda(B)<=w(t)*(B-x). "
                        + "The logarithmic growth estimate proves "
                        + "(t/B)^4*w(t)<=w(B). Exact integration of these "
                        + "bounds gives the endpoint moment bounds "
                        + "(t/B)^4*(B-2)^(-beta)*H^2/(2*t^(11/10)) "
                        + "<=a_beta(t)<=(t-2)^(-beta)*H^2/(2*t^(11/10)). "
                        + "Negative-power derivative estimates and "
                        + "H^2/t^(11/10)=sqrt(t) supply the displayed error. "
                        + "A triangle enters only as a proved bound on the "
                        + "same price-difference kernel.")),
                    Paragraph(Text(
                        "The source definition is EL Definition 1.2 in "
                        + "FIBONACCI_ATOMIC_RELATION_GENERATION_ROBIN_SELECTED_EULER_LAYERS. "
                        + "The estimate applies separately to every point "
                        + "of any complete original S_X contained in [4,infinity), "
                        + "for example when ell_X>=4; it does not select, "
                        + "thin or displace that family. At beta=1/2 its "
                        + "continuous single-window main term is 1/2.")),
                    Paragraph(Text(
                        "This is a continuous kernel supplier. It proves no "
                        + "integral interchange for W_X, no absolute lattice "
                        + "error and no discrete critical-threshold theorem. "
                        + "It does not identify a geometric trajectory with "
                        + "the original maximizing integers or prove their "
                        + "cofinal existence. The initialized seven-divisibility "
                        + "guard has mean p_0+p_25, including Q=0; its testing "
                        + "error is not Lambda-1 or I_X. The proposed calibration "
                        + "s=x-3, mass-action flow, entropy and Fisher-action "
                        + "claims remain outside this theorem. The full signed "
                        + "Robin/RH obligation remains open."))),
                DescribeRole.Theorem))));
}
