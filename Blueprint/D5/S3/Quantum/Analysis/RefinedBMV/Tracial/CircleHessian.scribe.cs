using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.Tracial;

internal sealed class CircleHessianDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two-insertion bound for the four-copy trace",
        H("Two-insertion bound for the four-copy trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-four-mark-trace-hessian"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/Tracial/CircleHessian.fourMarkTraceHessian_lower"),
                H("Signed trace bound by the commutator energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "In a common eigenbasis for the drift and the Hermitian second factor, integrate " +
                    "the trace of two perturbation insertions against the independent and periodic arc " +
                    "counts. The resulting quadratic coefficient dominates the squared Frobenius " +
                    "norm of the commutator multiplied by the second factor. The bound permits " +
                    "signed eigenvalues and has no dependence on the dimension or spectral gaps."))),
                DescribeRole.Theorem))));
}
