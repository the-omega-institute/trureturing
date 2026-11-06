using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattyOddWrapGaussianEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coupled finite logarithmic errors give a strict Gaussian lower envelope for the complete original odd-wrap return counts.",
        H("A strict finite Gaussian envelope for the original quotient returns"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-odd-wrap-gaussian-envelope"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattyOddWrapGaussianEnvelope.actual_gaussian_envelope"),
                H("The exact normalized count ratio strictly exceeds exp(s)+exp(-9s)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let p,t be integers with p>=3 odd and 2<=t<=p. Put s=4p^2/(p(6t-1)+1). At m=6t-1 and source length (p*m).toNat, let W19 and W33 be the complete existing original (1,9) and (3,3) quotient return counts. The finite theorem proves exp(s)+exp(-9s)<2W19/W33. Composite odd p and both t endpoints are included.")),
                    Paragraph(Text("Write a=3pt, n=p(6t-1), R=n+1, A=choose(n,a), B=choose(n,a+p), and D=choose(n,a+4p). The existing adjacent-binomial product identity choose_ratio_prod represents A/B by p symmetric factors with x_i=(p+2i+1)/R. It represents B/D by 3p symmetric factors with y_j=(3p+2j+1)/R. All x_i lie in [0,1), all y_j lie in [0,9/11], and A,B,D are positive on the full stated domain.")),
                    Paragraph(Text("Reuse the original first-moment identity sum_linear. An exact cubic moment gives X3=sum(x_i^3)=2p^2(5p^2-1)/R^3 and Y3=sum(y_j^3)=18p^2(45p^2-1)/R^3. Thus X3>0 and Y3<=(909/11)X3. The existing logarithm series bounds yield L=log(A/B)>=s+(2/3)X3 and M=log(B/D)<=9s+(121/20)Y3. In particular L>s and M<=9s+750(L-s), since the exact combined coefficient is 29997/40<750.")),
                    Paragraph(Text("The condition t<=p gives s>=2/3. A finite exponential certificate proves exp(20/3)>750, hence exp(10s)>750. For delta=L-s>0, the tangent-line inequality exp(u)>=1+u at both u=delta and u=-750delta yields exp(L)+exp(-M)>exp(s)+exp(-9s). This absorbs the larger second-block error using the strictly positive first-block error; it assumes no asymptotic limit or uncontrolled remainder.")),
                    Paragraph(Text("Finally the existing original formulas W19=2(A+D) and W33=4B identify exp(L)+exp(-M)=(A+D)/B=2W19/W33. All integer-to-natural index conversions and the original quotient readouts are retained. The result is a strict lower envelope on 2<=t<=p; it supplies neither an upper envelope nor an exact threshold or rounding formula. No literature novelty or complete open-problem settlement is claimed."))),
                DescribeRole.Theorem))));
}
