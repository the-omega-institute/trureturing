using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PetzRetainedQubitPairingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite spectral blocks bound the squared trace error for the ordinary Petz channel.",
        H("Ordinary Petz recovery for separated qubit spectra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("petzretainedqubitpairing-logisticcorrelation"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.logisticCorrelation"),
                H("Logistic Fourier correlation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Fourier correlation of the upper strip weight is K(t) = (t/2)/sinh(t/2), with K(0) = 1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("petzretainedqubitpairing-ordinary-petz-tracenorm-sq-le-of-qubit-gaps"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/PetzRetainedQubitPairing.ordinary_petz_traceNorm_sq_le_of_qubit_gaps"),
                H("Ordinary Petz error with retained support rank at most two"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Divergence/yang2026quantumdataprocessing")),
                Blocks(Paragraph(Text("For every finite CPTP channel and reference state, the ordinary Petz channel recovers the reference exactly. Its action uses the actual Kraus adjoint, the inverse square root on the positive output spectrum and the reference-state replacement on the complementary support.")),
                    Paragraph(Text("For each supported source, let Δ be the finite trace-log Umegaki entropy loss. If the reference output has rank at most two and the source output has rank at most one, the squared full trace norm error is bounded by 8Δ. If the reference output has rank at most two, the source output has rank two, and both positive output log-eigenvalue differences have K at most 1/5, the squared error is at most (8 + 2√2)Δ.")),
                    Paragraph(Text("The mixed source and reference eigenbases give opposite blocks with equal unitary-entry moduli. Hermiticity of the physical square roots ties the off-diagonal amplitudes to their adjoints. The centered logistic determinant controls both blocks at once, and the Stinespring strip comparison and Gram endpoint transfer the bound to the ordinary recovered state."))),
                DescribeRole.Theorem))));
}
