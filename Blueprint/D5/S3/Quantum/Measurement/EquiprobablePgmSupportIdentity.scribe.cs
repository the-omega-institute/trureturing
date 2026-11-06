using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class EquiprobablePgmSupportIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/EquiprobablePgmSupportIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The centered Hilbert-Schmidt dispersion identity uses the original priors and the actual spectral support inverse quarter power. Singular averages are allowed. It explains the baseline of the active-set comparison, and does not order the full and restricted bounds.",
        H("Original-prior PGM dispersion on singular support"),
        Blocks(
            Node("support_quarter_normalization", "Moore-Penrose quarter-power normalization",
                "For every finite index type n and every positive semidefinite complex n-by-n matrix Q, put R=Q^(-1/4) using the existing continuous functional calculus. Then R R=Q^(-1/2) and R Q R=sqrt(Q). The scalar negative powers are zero at the zero eigenvalue. Thus these are Moore-Penrose powers and no inverse or full-rank assumption is hidden in the notation."),
            Node("centered_identity", "The complete centered score identity",
                "Let N>0, let rho_i be positive semidefinite matrices on C^d with trace one, and let B be any nonempty subset of Fin N, with m=|B|. Put sigma_i=rho_i/N, S_B=sum_(i in B) sigma_i and R_B=S_B^(-1/4). With the existing pgmScore and squared Frobenius norm RHLinalg.frobSq=Re tr(X†X), the exact identity is P_B-1/N=sum_(i in B) ||R_B sigma_i R_B-(1/m)sqrt(S_B)||_F^2. The original weights 1/N are retained; this is not the renormalized m-label score. The proof first sums the sandwiches to sqrt(S_B), expands the finite variance, identifies each actual PGM trace term by cyclicity, and uses tr(S_B)=m/N. It includes m=1 and N=1, zero eigenvalues, repeated eigenvalues, and noncommuting states. A zero-dimensional state space cannot satisfy the trace-one hypotheses for a nonempty B."),
            Node("random_guessing_le", "The nonnegative original-prior advantage",
                "Under exactly the density and nonempty-label hypotheses of the centered identity, P_B>=1/N because every squared Hilbert-Schmidt term is nonnegative. In particular singularity does not invalidate the baseline. No comparison between two differently normalized averages follows from this nonnegativity."),
            Paragraph(Text("Source: the anonymous manuscript Why the Active-Set PGM Comparison Can Fail, 3 November 2026, section 2. Its anonymous attribution is retained and no license grant was supplied for that manuscript. The separate 4 November 2026 note is by Haobo Ma and Wenlin Zhang, in that order, and credits Hyunho Cha for the symmetric scores, qubit slice and commuting controls; its CC BY 4.0 license applies only to that new note. The earlier actual rational refutation remains EquiprobablePgmActiveSetRefutation.result, based on the literal byline Wenlin Zhang and Haobo / trureturing. This module does not duplicate that refutation.")),
            Paragraph(Text("The actual score definition is reused from EquiprobablePgmActiveSetRefutation.pgmScore. The Frobenius definition and Hermitian expansion are reused from the RHLinalg owners; their existing source attributions and licenses are unchanged. The two separate valid discrimination upper bounds, actual active-label reduction, universal parameter families, and the remaining all-pure and spectral-floor questions are separate obligations."))
        ), []));

    private static DocumentBlock Node(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("pgm-support-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromLean(),
        AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuantumBounds/anonymous2026pgmmechanism")), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
