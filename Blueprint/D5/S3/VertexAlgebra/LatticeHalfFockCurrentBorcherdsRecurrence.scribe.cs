using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockCurrentBorcherdsRecurrenceDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full signed original current Borcherds identity",
        H("Full signed original current Borcherds identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentborcherdsrecurrence-seed"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_current_minus_one_borcherds"),
                H("The corrected seed at every signed half-mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The literal Corr multiplication seed at mode one half extends by physical split crossings. Each adjacent crossing consumes the original current commutator; signed integer induction crosses only finitely many modes. The original fields and source states are unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentborcherdsrecurrence-forward"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.discrepancy_forward"),
                H("The forward discrepancy recurrence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The discrepancy at order n+1 is the difference of discrepancies at order n, evaluated at the adjacent half-mode and with cover exponent decreased by two. Each side is the original pointwise current residue. The proof uses finite Pascal telescoping and preserves the signed integer phase of the second right term."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentborcherdsrecurrence-nonnegative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_nonnegative_current_borcherds"),
                H("Every nonnegative current product order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original current commutator gives product order zero. The finite forward discrepancy recurrence then proves the actual identity at every nonnegative order, with arbitrary signed half-mode, cover exponent, original second source and actual tensor target."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentborcherdsrecurrence-backward"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.discrepancy_backward"),
                H("The physical translation discrepancy recurrence"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("Original source translation covariance and the physical derivative of Ytw give the backward discrepancy recurrence. Its coefficient is (E+2j+3)/2. Source, first-right and second-right supports justify every distribution and reindexing before the signed generalized-binomial cancellation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockcurrentborcherdsrecurrence-full"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockCurrentBorcherdsRecurrence.actual_signed_current_borcherds"),
                H("Every integer current product order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The original current commutator starts the nonnegative induction. The genuinely corrected minus-one seed starts the negative induction; the backward recurrence divides only by its nonzero integer order. The resulting exact pointwise finite residues agree for arbitrary integer product order, signed half-mode and cover exponent, arbitrary original second source, and actual tensor target, assuming only lattice data and invertibility of its Gram determinant.")),
                    Paragraph(Text("This is the current-generator twisted Borcherds identity, not arbitrary-first-source twisted Jacobi. No positivity, inverse-Gram choice, vacuum target, occupation cutoff or assumed seed/module law is used. Full string-theoretic and AdS/CFT bridges remain outside this result."))),
                DescribeRole.Theorem))));
}
