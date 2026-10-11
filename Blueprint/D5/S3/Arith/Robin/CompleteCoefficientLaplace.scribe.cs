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
                "SOURCE ONLY / UNCOMPILED: every accompanying D5 and Reg declaration "
                + "awaits the caller's scoped compilation, exact-source review and axiom checks. "
                + "This narrative records intended mathematics, not an acceptance receipt.")),
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
                        "The intended theorem proves physical integrability, the exact "
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
                        "The source APIs were inspected at Mathlib "
                        + "db584cd6d46c92f209a44c0f1c829460d327499d, Lean v4.33.0. "
                        + "Literal M1, H1, H2, U2, GJ1, GJ2 and the signed consumer "
                        + "were read at project pin 7f52221f2e23da81475058d5b5b6620e68709401. "
                        + "The original signed formula is attributed there to "
                        + "Broadbent-Fiori-Kadiri-Ng-Wilk, Bounds for Mertens sums, "
                        + "Proposition 13(i), equation (55), proof (82)-(83). "
                        + "The ordinary audit is provenance and a plan, not this "
                        + "worker's independent verification. No priority is claimed.")),
                    Paragraph(Text(
                        "The entire H1 remainder is retained. Finite-endpoint U2 is "
                        + "unchanged. Positivity of the numerator gives no real sign "
                        + "for F_A or for the signed actual-zero response. Gamma damping, "
                        + "both ordinate signs, all multiplicities and beta values, "
                        + "the full tail, elementary corrections, directed arithmetic "
                        + "comparisons and reserve/defect require their own consumers. "
                        + "Robin and RH are not accepted by this source implementation.")),
                    Paragraph(Text(
                        "The matching Reg source attempts the existing DependentFamily "
                        + "template on the full telescope, retaining the real physical "
                        + "axis, nonintegrable constant intervention, role sensitivity "
                        + "and actual observation dependence. It is unvalidated: "
                        + "compiler-derived sourceSelection and binding evidence are "
                        + "absent and every proof is uncompiled. No template defect "
                        + "or applicability of issue 5214 was established. There are "
                        + "no intentionally omitted D5 proof blocks or conclusion "
                        + "hypotheses, but elaboration and all required checks remain open."))),
                DescribeRole.Theorem))));
}
