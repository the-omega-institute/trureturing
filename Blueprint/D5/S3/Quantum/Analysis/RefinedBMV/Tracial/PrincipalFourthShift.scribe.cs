using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.Tracial;

internal sealed class PrincipalFourthShiftDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Quantum/Analysis/RefinedBMV/Tracial/PrincipalFourthShift.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A spectral criterion for the refined BMV four-copy lower bound",
        H("A spectral criterion for the refined BMV four-copy lower bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-four-positive-index-shift"),
                DeclarationHandle.Create(Module + "diagonal_word_bound_shift_of_posIndex_fiber_trace_nonneg"),
                H("Nonnegative scalar shifts of the second factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The four-copy lower bound holds when the second factor is a nonnegative scalar " +
                    "shift of a Hermitian matrix with positive index at most one and nonnegative traces " +
                    "on the spectral subspaces of the first factor. A unitary acting within each spectral " +
                    "subspace makes the compression's diagonal constant. The principal minor signs " +
                    "then control the word gap before and after the scalar shift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refined-bmv-four-spectral-mean-threshold"),
                DeclarationHandle.Create(Module + "product_bound_of_second_eigenvalue_le_fiber_trace"),
                H("Second eigenvalue and spectral block means"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Let the first factor have nonnegative eigenvalues. Suppose a nonnegative scalar " +
                    "is at least the second largest eigenvalue of the Hermitian second factor and at most " +
                    "its mean diagonal entry on every nonempty spectral subspace of the first factor. " +
                    "Then the mean trace of the ordered words with any number of first factors and " +
                    "four second factors dominates the balanced product trace."))),
                DescribeRole.Theorem))));
}
