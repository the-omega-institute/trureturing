using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class LiReflectedKernelDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/ZeroData/LiReflectedKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reflection gives an inverse-square majorant for the actual Li resolvent kernels.",
        H("Uniform Convergence of Reflected Li Kernels"),
        Blocks(
            Paragraph(Text(
                "Let Z enumerate all actual nontrivial zeta zeros without repetition, "
                    + "with exact analytic multiplicities m_k. Put rho_k=Z.zero(k), "
                    + "gamma_k=-i*(rho_k-1/2), q_k=1-1/rho_k, and "
                    + "r_k=1-1/(1-rho_k). Define "
                    + "Phi_k(z)=m_k/2*(2/(1-z)-q_k/(1-q_k*z)-r_k/(1-r_k*z)). "
                    + "The operation pairs reflection rho with 1-rho; it does not "
                    + "identify reflection with complex conjugation.")),
            Describe.Lean(
                DescribeId.Create("reflected-li-kernel-uniform-convergence"),
                DeclarationHandle.Create(Owner + "reflected_li_kernel_uniform_convergence"),
                H("A fixed disk and a summable tail"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every actual-zero presentation Z and every k with "
                            + "|gamma_k|>=2, the bound "
                            + "|Phi_k(z)|<=4*m_k/(1+|gamma_k|^2) holds whenever |z|<=1/4. "
                            + "For every point of that closed disk the series of norms "
                            + "is summable. Moreover, the complex sums over finite subsets "
                            + "of the indices converge uniformly on the closed disk to "
                            + "the infinite sum. The finite subsets are ordered by inclusion; "
                            + "no particular ordering of the zeros is required.")),
                    Paragraph(Text(
                        "Set D_k=rho_k*(1-rho_k)=gamma_k^2+1/4 and x_k=1/D_k. "
                            + "Then q_k*r_k=1 and q_k+r_k=2-x_k. Where the denominators "
                            + "are nonzero, the rational "
                            + "expression in parentheses is "
                            + "x_k*(1+z)/((1-z)*((1-z)^2+x_k*z)). "
                            + "The tail condition gives |x_k|<=1/2 and "
                            + "|x_k|<=2/(1+|gamma_k|^2). "
                            + "On the disk, |1-z|>=3/4, |1+z|<=5/4, and "
                            + "|(1-z)^2+x_k*z|>=7/16. "
                            + "Thus the collapsed expression has norm at most 4*|x_k|, "
                            + "giving the stated majorant after multiplication by m_k/2.")),
                    Paragraph(Text(
                        "The existing actual-zero reciprocal-square weight theorem "
                            + "makes the majorant summable. Only finitely many indices "
                            + "have |gamma_k|<2. Their terms are retained, and a "
                            + "cofinite Weierstrass estimate gives the uniform limit. "
                            + "No Riemann hypothesis or numerical lower bound for zero "
                            + "heights is assumed.")),
                    Paragraph(Text(
                        "These are convergence statements. They do not identify the "
                            + "sum with the completed-zeta logarithmic derivative, nor "
                            + "identify its Taylor coefficients with Li's derivative "
                            + "coefficients. At singular arguments, the displayed inverses "
                            + "use the field convention that the inverse of zero is zero. "
                            + "To differentiate the sum, one must also "
                            + "choose a neighborhood with no poles in the finite head; "
                            + "uniform convergence alone does not supply that condition. "
                            + "The classical zero-sum conventions are those of Li, "
                            + "Journal of Number Theory 65 (1997), 325-333, and "
                            + "Bombieri and Lagarias, Journal of Number Theory 77 "
                            + "(1999), 274-287."))),
                DescribeRole.Theorem))));
}
