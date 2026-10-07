using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class PrimePrefixOriginalShoulderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same complete original shoulder has a strict uniform half-gamma reserve.",
        H("The Complete Original Normalized-Zeta Shoulder"),
        Blocks(
            Paragraph(Text(
                "Retain the literal two-piece constant A from PrimePrefixOriginalA, "
                + "Q(u)=u*Re(zeta(1+u)), C=exp(Euler's constant), and k=C-1. "
                + "The original shoulder is K(t)=A-k*(log(t)+Euler's constant) "
                + "+C*integral over every u>0 of exp(-t*u)*(1/Q(u)-1)/u.")),
            Describe.Lean(
                DescribeId.Create("prime-prefix-original-shoulder"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/PrimePrefixOriginalShoulder.result"),
                H("Complete integrability and a strict supremum reserve"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For delta=(2*log(2)-1)/6, the theorem proves delta>0 and "
                        + "absolute integrability of the entire literal shoulder kernel "
                        + "at every t>0. It supplies the shared upper bound "
                        + "K(t)<=A-Lambda(k)-m(k), with "
                        + "Lambda(k)=k*(1+log((1+k)/(2*k))) and "
                        + "m(k)=k*exp(-2/k)*(log(2)-1/2).")),
                    Paragraph(Text(
                        "The strict supremum satisfies sup K < "
                        + "-1/6-(3/2)*delta*exp(-4), and also the earlier "
                        + "sup K < -delta*(1+exp(-6)). A common fixed barrier pays "
                        + "strictness for the supremum over all t>0.")),
                    Paragraph(Text(
                        "The original macro secant bound and the actual right zeta "
                        + "residue give Q(u)>=1+u/2 on u>0. The consumed complete "
                        + "Bose/Gamma normalization gives Q(u)<=1+u. Together these "
                        + "prove the kernel is bounded in absolute value by 1 and "
                        + "is at most -1/(u+2). The affine full-integral substitution "
                        + "y=t*(u+2) supplies the original complete comparison.")),
                    Paragraph(Text(
                        "The full logarithmic tail FTC turns that comparison into "
                        + "a unit-mass exponential average of "
                        + "k*(log(y/2)+Euler's constant)+1/y. Its scalar gap above "
                        + "Lambda(k) is nonnegative, and its complete tail beyond "
                        + "x+2/k has mass exp(-2/k) and a positive fixed gap. "
                        + "That tail supplies m(k) without truncation.")),
                    Paragraph(Text(
                        "The existing Euler constant bound gamma>1/2 gives k>1/2. "
                        + "The lower logarithmic tangent gives "
                        + "Lambda(k)>=2*k/(1+k)>2/3 and the tail reserve is "
                        + "m(k)>(3/2)*delta*exp(-4). Combined with the original "
                        + "A<1/2, these prove the stronger explicit bound.")),
                    Paragraph(Text(
                        "The literal definitions and macro estimate retain the "
                        + "PrimePrefixMacroProfile and PrimorialGlobalLaplaceEnvelope "
                        + "provenance. Private consumed Bose/Gamma supplier bodies "
                        + "retain the classical Gamma/Bose attribution and the "
                        + "FermiMellin attribution to David Sanftenberg (2026), "
                        + "Apache-2.0. Complete logarithmic FTC and integrability "
                        + "retain Mertens.Gamma and PrimePrefixOriginalA provenance. "
                        + "The exponential-average argument is actual-prefix "
                        + "theory section 447; the half-gamma reserve strengthens "
                        + "it in section 451. The remaining signed tail and full "
                        + "Robin pairing remain mathematical obligations."))),
                DescribeRole.Theorem))));
}
