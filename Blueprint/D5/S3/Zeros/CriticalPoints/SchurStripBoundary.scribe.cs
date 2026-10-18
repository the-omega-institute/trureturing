using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.CriticalPoints;

internal sealed class SchurStripBoundaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/CriticalPoints/SchurStripBoundary.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp right boundary trace estimate records exactly the phase information required by equality.",
        H("The right boundary and its equality phases"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("schur-strip-right-bound"),
                DeclarationHandle.Create(Prefix + "right_boundary_bound_and_phases"),
                H("The right boundary bound with phase rigidity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n>0, p>0, positive t_j, unit phases u_j, every real y and every unitary matrix K, the norm of Tr(K H(n,p(1+iy)/2) diag(u_j positivePower(t_j,p(1+iy))) H(n,p(1+iy)/2)) is at most M=((n+1)^p+n−1)/n times sum_j t_j^p. If equality holds, then u_i exp(ipy log t_i)=u_j exp(ipy log t_j) for every i,j. The explicit Hermitian-power columns have equal squared norms and pairwise nonzero inner products."))),
                DescribeRole.Theorem))));
}
