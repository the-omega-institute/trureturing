using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class CompleteCoefficientLaplaceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/CompleteCoefficientLaplace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal complete Robin coefficient has a Laplace resolvent and a factor-one modulus bound.",
        H("Complete Robin Coefficient Laplace Representation"),
        Blocks(
            Paragraph(Text(
                "The coefficient is defined by its complete physical integral. "
                + "The theorem retains physical and product integrability, exact "
                + "changes of variables, the full complex resolvent and factor one.")),
            Paragraph(Text(
                "For every real A>1 set L=log(A)>0. For 0<Re(s)<1 define the literal "
                + "physical coefficient F_A(s)=s^(-1)*integral over u>A of "
                + "u^(s-2)*(1+log(u))/log(u)^2. Positive real bases use their real "
                + "logarithm. The definition is the physical integral, not the resolvent.")),
            Describe.Lean(
                DescribeId.Create("complete-coefficient-laplace"),
                DeclarationHandle.Create(Prefix + "complete_coefficient_laplace"),
                H("The complete physical coefficient and its full resolvent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The theorem proves physical integrability, the exact "
                        + "logarithmic substitution F_A=s^(-1)*integral over x>L of "
                        + "exp((s-1)*x)*(1/x+1/x^2), product integrability of the actual "
                        + "K(x,t)=(1+t)*exp(-((1-s)+t)*x) on x>L,t>0, and integrability "
                        + "of the complete resolvent. It then gives "
                        + "F_A=A^(s-1)/s*integral over t>0 of (1+t)*exp(-L*t)/(1-s+t), "
                        + "and ||F_A||<=A^(Re(s)-1)*(1/L+1/L^2)/(||s||*||1-s||).")),
                    Paragraph(Text(
                        "Reuse n=0,1 of LiCausalTrichotomy's complex Laplace moments "
                        + "for numerator mass and integrability. The actual norm bound "
                        + "||K(x,t)||<=exp((Re(s)-1)*x)*(1+t)*exp(-L*t), together with "
                        + "Integrable.mul_prod, proves product integrability before "
                        + "integral_integral_swap. The x integral uses "
                        + "integral_exp_mul_complex_Ioi. integral_comp_exp_Ioi and its "
                        + "integrability equivalence bind the physical integral with "
                        + "the true Jacobian. The denominator norm-square difference "
                        + "2*t*(1-Re(s))+t^2 is nonnegative; the norm-integral inequality "
                        + "and the two exact numerator moments give factor one.")),
                    Paragraph(Text(
                        "The physical coefficient is M1 in "
                        + "Library/ArithSums/nicolas2025comparison.md. "
                        + "Its signed explicit formula is attributed there to "
                        + "Broadbent-Fiori-Kadiri-Ng-Wilk, Bounds for Mertens sums, "
                        + "Proposition 13(i), equation (55), proof (82)-(83). "
                        + "The coefficient identity here does not certify that "
                        + "published signed formula. No priority is claimed.")),
                    Paragraph(Text(
                        "This is the complete coefficient, including the H1 remainder; "
                        + "it does not replace the finite-endpoint U2 estimate. "
                        + "Positivity of the numerator gives no real sign "
                        + "for F_A or for the signed actual-zero response. Gamma damping, "
                        + "both ordinate signs, all multiplicities and beta values, "
                        + "the full tail, elementary corrections, directed arithmetic "
                        + "comparisons and reserve/defect require their own consumers. "
                        + "Robin and RH remain outside the coefficient theorem."))),
                DescribeRole.Theorem))));
}
