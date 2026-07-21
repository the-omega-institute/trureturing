using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class MatrixUnitsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Schwinger =
        LibraryNoteRef.Create("D5/L/schwinger1960unitary");
    private static readonly LibraryNoteRef Murphy =
        LibraryNoteRef.Create("D5/L/murphy1990calgebras");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Quantum/MatrixUnits",
            "Construct exact finite Weyl pairs and the matrix-unit structure of full complex matrix algebras."),
        H("Finite Weyl Pairs and Matrix Units"),
        Blocks(
            Paragraph(Text(
                "The six theorems below are internal statements about explicitly constructed finite complex matrices. They do not identify an arbitrary observer window with a full matrix algebra; prime-power tensor factorization remains residual, and the general Robertson variance inequality remains residual. The no-character theorem is not upgraded to Kochen-Specker, CHSH, hidden-address locality, or a probability interpretation.")),
            new DocumentBlock.Describe(
                DescribeId.Create("constructed-finite-weyl-relation"),
                DescribeKind.Theorem,
                H("The constructed finite shift and phase matrices obey the Weyl relation"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/MatrixUnits.qudit_weyl_relation")),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "For every positive dimension n, omega is defined as exp(2 pi i/n), V is the permutation matrix of the canonical rotation of Fin n, and U is diagonal with entries omega^r. Lean proves VU = omega UV from these definitions. No desired commutation relation is carried as an assumption, and no observer-window generation claim is inferred."))),
                LatexStatement.Create(@"$$\forall n>0,\quad V_nU_n=\omega_n U_nV_n,\qquad \omega_n=\exp(2\pi i/n)$$")),
            new DocumentBlock.Describe(
                DescribeId.Create("constructed-phase-has-finite-order"),
                DescribeKind.Theorem,
                H("The constructed phase matrix has finite order"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/MatrixUnits.qudit_phase_order")),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "The canonical root is primitive of order n, so the explicit diagonal phase matrix satisfies U_n^n = I. This is exact finite-register algebra and does not establish prime-power tensor factorization."))),
                LatexStatement.Create(@"$$\forall n>0,\quad U_n^n=I_n$$")),
            new DocumentBlock.Describe(
                DescribeId.Create("constructed-shift-has-finite-order"),
                DescribeKind.Theorem,
                H("The constructed cyclic shift has finite order"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/MatrixUnits.qudit_shift_order")),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "The canonical rotation of Fin n returns after n steps, and its permutation matrix therefore satisfies V_n^n = I. The proof derives the matrix power from the permutation power rather than assuming cyclicity."))),
                LatexStatement.Create(@"$$\forall n>0,\quad V_n^n=I_n$$")),
            new DocumentBlock.Describe(
                DescribeId.Create("matrix-unit-certificate-error-is-zero"),
                DescribeKind.Theorem,
                H("Matrix-unit multiplication and adjoint certificates have zero error"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/MatrixUnits.matrix_unit_certificate_error_zero")),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "For every finite decidable index type, the multiplication residual E_ij E_kl - delta_jk E_il and the adjoint residual E_ij^* - E_ji are literally the zero matrix. There is no floating-point tolerance or numerical proxy."))),
                LatexStatement.Create(@"$$E_{ij}E_{kl}-\delta_{jk}E_{il}=0\quad\land\quad E_{ij}^{*}-E_{ji}=0$$")),
            new DocumentBlock.Describe(
                DescribeId.Create("matrix-units-generate-the-full-algebra"),
                DescribeKind.Theorem,
                H("Matrix units generate the full finite matrix algebra"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/MatrixUnits.matrix_units_generate_full_algebra")),
                DescribeProvenance.LiteratureAttested(Schwinger),
                Blocks(Paragraph(Text(
                    "Every finite complex square matrix is a finite linear combination of standard matrix units, so their complex algebraic adjoin is the top subalgebra. The ambient type is already a full matrix algebra; this theorem does not identify an arbitrary observer window with it."))),
                LatexStatement.Create(@"$$\operatorname{adjoin}_{\mathbb{C}}\{E_{ij}:i,j\in I\}=M_I(\mathbb{C})$$")),
            new DocumentBlock.Describe(
                DescribeId.Create("all-nontrivial-full-matrix-algebras-have-no-character"),
                DescribeKind.Theorem,
                H("Every nontrivial full complex matrix algebra has no character"),
                DescribeStatement.FromLean(LeanTheorem(
                    "D5/S3/Quantum/MatrixUnits.matrix_algebra_has_no_character")),
                DescribeProvenance.LiteratureAttested(Murphy),
                Blocks(Paragraph(Text(
                    "For every finite index type with at least two elements, no unital complex-algebra homomorphism from the full square matrix algebra to the complex numbers exists. This proves the all-matrix-sizes character obstruction without weakening it to a partial value table. Kochen-Specker projection valuations, CHSH bounds, hidden-address locality, and probability conclusions remain separate residuals."))),
                LatexStatement.Create(@"$$|I|\geq 2\quad\Rightarrow\quad \operatorname{IsEmpty}\!\left(M_I(\mathbb{C})\to_{\mathbb{C}\text{-alg}}\mathbb{C}\right)$$")))));
}
