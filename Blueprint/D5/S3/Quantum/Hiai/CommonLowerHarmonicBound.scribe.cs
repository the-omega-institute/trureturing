using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Hiai;
internal sealed class CommonLowerHarmonicBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common positive lower matrix and a complex split", H("CommonLowerHarmonicBound"), Blocks(
            Describe.Lean(DescribeId.Create("common-split"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/CommonLowerHarmonicBound.common_lower_split_bound"),
                H("A common positive lower matrix and a complex split"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For every split W1+W2=I, the common lower matrix K is bounded by twice the split energy. Both inputs can be singular. The residual for the equal K inputs is (W1-W2) adjoint times K times (W1-W2); monotonicity in each input gives the bound. The split matrices themselves can be arbitrary complex matrices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("harmonic-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Hiai/CommonLowerHarmonicBound.common_lower_harmonic_bound"),
                H("Harmonic domination without inverting the lower matrix"), StatementSource.FromLean(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/codex2026productmargin")),
                Blocks(Paragraph(Text("For positive definite P and Q, every PSD K with K at most P and Q is at most twice their parallel sum, and the same comparison holds after taking the real trace. The proof applies the attained split from ParallelSumVariational.parallel_sum_minimum to the preceding general split bound. K may be singular and may fail to commute with either input."))), DescribeRole.Theorem))));
}
