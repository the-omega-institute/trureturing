using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class ForwardKernelMellinResidueDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernelMellinResidue.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original complete forward response has a Mellin continuation with the prescribed zeta principal term.",
        H("The Mellin identity for the original forward price kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forward-kernel-mellin-residue"),
                DeclarationHandle.Create(Prefix + "forward_kernel_mellin_residue"),
                H("A holomorphic remainder beyond the critical line"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Weil/nist2026criticalzeros")),
                Blocks(
                    Paragraph(Text(
                        "Assume there is a real C such that |psi(t)-t|<=C*sqrt(t)*log(t)^2 "
                        + "for every real t>=2. For each x0>=3, let F(s) be the actual "
                        + "Lebesgue Mellin integral of the normalized original forward "
                        + "response T(x). There is R holomorphic on Re(s)>-1/5 such that, "
                        + "for Re(s)>1/2, F(s)=-zeta'(s+1/2)/(2*zeta(s+1/2)) "
                        + "-1/(2*(s-1/2))+R(s). The displayed Chebyshev estimate is "
                        + "the only classical hypothesis; RH is not an additional assumption.")),
                    Paragraph(Text(
                        "Absolute Fubini gives the complete signed adjoint. Above a "
                        + "fixed cutoff, its inverse-coordinate form is t^(-s-1/2)/2 "
                        + "plus the proved remainder r(t,s). Partial summation identifies "
                        + "the signed remainder tail with -E(a)*r(a,s) minus the integral "
                        + "of E(t)*partial_t r(t,s). Its uniform derivative estimate and "
                        + "the assumed Chebyshev bound give holomorphy on Re(s)>-1/5. "
                        + "The finite signed correction is entire. The principal term "
                        + "is the complete von Mangoldt Dirichlet series minus the "
                        + "Lebesgue density. A final compact-center Mellin correction "
                        + "extends the lower endpoint from x0>=4 to every x0>=3.")),
                    Paragraph(Text(
                        "The original integral is absolutely integrable for Re(s)>1/5. "
                        + "The identity is initially asserted on Re(s)>1/2, and supplies "
                        + "a continuation through its explicit zeta principal term. "
                        + "No separate multiplicity or residue corollary is asserted here."))),
                DescribeRole.Theorem))));
}
