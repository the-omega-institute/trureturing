using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class ActualChannelAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "These declarations are consumed helpers for the original whole ST37 theorem. They organize the actual channel algebra and reuse the existing pointwise theorem; they are not independent claims of new mathematical content.",
        H("ActualChannelAlgebra"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("input-choi-index-swap"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/ActualChannelAlgebra.inputChoi_index_swap"),
                H("inputChoi index swap"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("The input-first Choi matrix is exactly the standard Choi matrix pulled back along the swap of its product indices. This identifies the convention used by the original ST37 channel and the pinned complete-positivity API."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("input-choi-pos-semidef"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/ActualChannelAlgebra.inputChoi_posSemidef"),
                H("inputChoi posSemidef"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("Complete positivity of the actual complex matrix map makes its input-first Choi matrix positive semidefinite. The proof transports the existing Choi positivity criterion through the product-index equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kraus-normalization-from-actual-trace"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/ActualChannelAlgebra.kraus_normalization_from_actual_trace"),
                H("kraus normalization from actual trace"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("For an arbitrary finite rectangular Kraus family, trace preservation on every complex input matrix implies that the sum of the adjoint Gram matrices is the identity. Evaluation on every complex matrix unit determines every entry of this normalization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-sqrt-columns-kraus"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_sqrt_columns_kraus"),
                H("actual sqrt columns kraus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("The actual CFC square root of the input-first Choi matrix is reshaped column by column. Its specified rectangular columns reconstruct the channel on every complex matrix, and trace preservation gives their adjoint Gram sum equal to the identity. The family is the original redundant family, without selecting a minimal Kraus representation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-cptp-left-inverse-spectral-algebra"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_cptp_left_inverse_spectral_algebra"),
                H("actual cptp left inverse spectral algebra"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("With only positive input dimension, complete positivity, trace preservation and an actual completely positive trace-preserving left inverse, spectral whitening defines a supported unital star representation. The actual support and inverse square root retain their CFC definitions. The representation commutes with the channel identity value and recovers the original channel after multiplication by that value."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-cptp-left-inverse-syndrome-rank"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_cptp_left_inverse_syndrome_rank"),
                H("actual cptp left inverse syndrome rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("For the actual whitened matrix units, the rank of the distinguished diagonal matrix unit is k when the support rank is k times the positive input dimension. The proof uses the existing pointwise isometric tensor factorization and the finite-dimensional rank formula, retaining all original natural-number cases."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-input-choi-rank"),
                DeclarationHandle.Create("D5/S3/Quantum/Recovery/ActualChannelAlgebra.actual_inputChoi_rank"),
                H("actual inputChoi rank"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                    LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
                Blocks(Paragraph(Text("The actual input-first Choi rank is k under the original reversible-channel hypotheses and support rank k times d. The input-first Choi matrix factors through its distinguished diagonal block N(e_vv), and that same block is a submatrix of the Choi matrix. The block has rank k by whitening and the existing syndrome-rank calculation. Both rank inequalities therefore give equality. This is an actual channel rank identity, not an assumption supplied to the smooth square-root step."))),
                DescribeRole.Theorem))));
}
