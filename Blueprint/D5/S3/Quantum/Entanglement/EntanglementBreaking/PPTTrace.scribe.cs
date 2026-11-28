using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EntanglementBreaking;

internal sealed class PPTTraceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Resource/devendra2023mapping");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Output partial transpose and trace separation of decomposable maps.",
        H("Trace separation for decomposable maps"),
        Blocks(
            Describe.Lean(DescribeId.Create("eb-ppttrace-isdecomposable"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.IsDecomposable"),
                H("Decomposability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("The positive summand has positive left amplification at every positive integer dimension. The second summand has the same property after transpose on its output. Their sum equals the given complex-linear map."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-ppttrace-choicandidate"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.choiCandidate"),
                H("Choi matrix from a Hermitian direction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a matrix H on the product of two copies of dimension d, the candidate is the identity minus (16/d) times H."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-ppttrace-ppttest"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.pptTest"),
                H("Trace test from a Hermitian direction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The test is the unnormalized matrix I + H/(4d)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("eb-ppttrace-indecomposable-of-ppt-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.indecomposable_of_ppt_trace"),
                H("Negative trace pairing excludes decomposability"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The Choi matrix of a decomposable map is the sum of a positive semidefinite matrix and the output partial transpose of another positive semidefinite matrix. Pairing with a positive semidefinite matrix that has positive semidefinite partial transpose is nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-ppttrace-candidate-trace-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.candidate_trace_bound"),
                H("Energy gives a negative trace pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Tracelessness cancels the terms linear in H. The quadratic contribution is negative and the lower bound on the real trace of H squared forces the unnormalized pairing to be at most minus d squared."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-ppttrace-inputchoi-decomposition"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.inputChoi_decomposition"),
                H("Input choi decomposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A decomposition of the map into completely positive and completely copositive parts gives an input-first Choi decomposition P plus the output partial transpose of Q, with P and Q positive semidefinite."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-ppttrace-partialtranspose-trace-pairing-of-psd"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.partialTranspose_trace_pairing_of_psd"),
                H("Partial transpose trace pairing of psd"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For complex matrices on a finite product space and a positive semidefinite first matrix Q, move its output partial transpose across the trace pairing with any matrix R."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("eb-ppttrace-candidate-indecomposable"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/EntanglementBreaking/PPTTrace.candidate_indecomposable"),
                H("Candidate indecomposable"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("In dimension d at least one, a traceless H with real trace of H squared at least d to the fourth power over two gives an indecomposable candidate whenever the trace test and its partial transpose are both positive semidefinite."))),
                DescribeRole.Theorem))));
}
