using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.LocalDold;

internal sealed class BackwardZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar and backward-zero local-Dold obstructions", H("Scalar and backward-zero local-Dold obstructions"), Blocks(
            Paragraph(Text("The historical supplied full proof bodies are reused. Matrix denominator clearing and scalar mismatch feed the general obstruction, which is consumed by the bilateral k-bonacci family and the literal printed sequences. Normalized impulse blocks are a distinct domain. Registration is unfinished under issue 29392; no declared_validated status is claimed.")),
            Describe.Lean(DescribeId.Create("backwardzero-dold-prime-congruence"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/BackwardZero.dold_prime_congruence"),
                H("dold_prime_congruence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/mazhang2026backwardzero")),
                Blocks(Paragraph(Text("For an integer sequence satisfying all positive-index Mobius divisibilities, a prime q and a positive m coprime to q, q divides u(mq)-u(m). No positivity of u is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("backwardzero-no-repair-of-unit-mismatch"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/BackwardZero.no_repair_of_unit_mismatch"),
                H("no_repair_of_unit_mismatch"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/mazhang2026backwardzero")),
                Blocks(Paragraph(Text("Let a be nonzero at all positive indices, p prime, L,m,r positive, r coprime to pL, and a(n+L p^j) congruent to a(n) modulo p^(j+1) at every positive n and every j. A mismatch between valuations at mr and m excludes every fixed positive multiplier of its local part. This is a scalar theorem; neither a vector mismatch nor the withdrawn unbounded-affine classification is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("backwardzero-kernel-orbit-no-repair"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/BackwardZero.kernel_orbit_no_repair"),
                H("kernel_orbit_no_repair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/mazhang2026backwardzero")),
                Blocks(Paragraph(Text("An integer matrix A, kernel observation l(y)=0, prime p not dividing det A, and strictly positive offset h with all forward observations at n+h nonzero give no positive local-Dold repair. The proof supplies a finite matrix period and a lifted scalar mismatch."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("backwardzero-adjugate-zero-of-backward-zero"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/BackwardZero.adjugate_zero_of_backward_zero"),
                H("adjugate_zero_of_backward_zero"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/mazhang2026backwardzero")),
                Blocks(Paragraph(Text("For an integer matrix with nonzero determinant, a rational backward observation l(A^(-h)x)=0 implies the integral observation l(adj(A)^h x)=0, with arbitrary natural h. The adjugate clears the rational denominator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("backwardzero-matrix-backward-zero-no-repair"),
                DeclarationHandle.Create("D5/S3/Arith/LocalDold/BackwardZero.matrix_backward_zero_no_repair"),
                H("matrix_backward_zero_no_repair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Scale/mazhang2026backwardzero")),
                Blocks(Paragraph(Text("Assume h>0, the rational backward observation vanishes, all positive-time integer forward observations are nonzero, and prime p does not divide det A. At every nonnegative shift s, no positive integer c makes c times p to the valuation of the observation at n+s Dold. Forward observations may have either sign; the valuation uses absolute value."))), DescribeRole.Theorem))));
}
