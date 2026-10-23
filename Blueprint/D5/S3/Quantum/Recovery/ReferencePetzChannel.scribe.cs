using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class ReferencePetzChannelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A reference-preserving full-space Petz channel.",
        H("A reference-preserving full-space Petz channel"), Blocks(
            Describe.Lean(
                DescribeId.Create("density-reset-kraus"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/ReferencePetzChannel.densityResetKraus"),
                H("Reference reset Kraus family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("This finite Kraus family realizes the completely positive reset X -> Tr(B X B*) S S*. It "
                        + "supplies the missing trace on the complement of the supported Petz core."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("complete-quantum-channel-with-reference"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/ReferencePetzChannel.complete_quantum_channel_with_reference"),
                H("Complete a supported Kraus map with a reference state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("A Kraus Gram sum equal to a self-adjoint projection P is completed by a reference-density "
                        + "reset on I-P. The conclusion is one bundled completely positive trace-preserving channel "
                        + "with its action proved on every input matrix. The proof uses an actual finite Kraus "
                        + "family, not an asserted positivity or trace law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("completed-reference-petz-channel"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/ReferencePetzChannel.completed_reference_petz_channel"),
                H("Canonical core plus reference complement"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/meiburg2026relative")),
                Blocks(Paragraph(Text("For a trace-preserving Kraus channel and a reference density sigma, use the spectral "
                        + "inverse square root of Q=Phi(sigma), totalized as zero on ker Q. The actual supported "
                        + "transpose core is completed by Tr((I-P_Q) X) sigma. The result acts on every matrix and "
                        + "restores sigma. Singular references remain allowed. The core alone generally has trace "
                        + "Tr(P_Q X); the complement term is essential for a full-space channel. This channel is "
                        + "consumed by CanonicalPetzEquality, where it is chosen before rho. The construction is "
                        + "established in Hiai-Mosonyi-Petz-Beny, Quantum f-divergences and error correction, "
                        + "arXiv:1008.2529, full-space completion following Theorem 5.1."))),
                DescribeRole.Theorem))));
}
