using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzSchwarzRecoveryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schwarz and trace rigidity give actual Petz recovery.",
        H("Schwarz and trace rigidity give actual Petz recovery"), Blocks(
            Describe.Lean(
                DescribeId.Create("petz-output-support-projection"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_output_support_projection"),
                H("The actual output lies in reference support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("Actual channel support transfer gives P_Q T = T without a full-rank assumption. The "
                        + "statement is used both in Schwarz trace rigidity and to annihilate the complement reset on "
                        + "Phi(rho)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-core-schwarz-and-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_core_schwarz_and_trace"),
                H("One shared Schwarz and trace supplier"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the actual model let H=sqrt(S), W=Q^(-1/2), Y=W sqrt(T), "
                        + "A=H Psi(Y), C=A P_R, and N=H Psi(W T W) H. The shared supplier proves "
                        + "A A* <= N, C C* <= N, and Tr(N)=Tr(R). The compressed bound follows from "
                        + "the orthogonal input support projection. Both exact recovery from support columns "
                        + "and the quantitative Petz core trace estimate consume these same facts; the "
                        + "Schwarz and trace proof is not duplicated."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("petz-core-recovery-of-support-columns"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzSchwarzRecovery.petz_core_recovery_of_support_columns"),
                H("Positive order plus equal trace forces recovery"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("From sqrt(S) Psi(Q^(-1/2) sqrt(T)) P_R = sqrt(R), the actual channel Schwarz inequality "
                        + "yields R <= M M* <= N, where N is the Petz core output. Actual trace pairing and output "
                        + "support give Tr N = Tr R. The positive semidefinite difference of trace zero vanishes, "
                        + "proving N=R. The theorem does not assume recovery or an unproved full-space identity for "
                        + "M."))),
                DescribeRole.Theorem))));
}
