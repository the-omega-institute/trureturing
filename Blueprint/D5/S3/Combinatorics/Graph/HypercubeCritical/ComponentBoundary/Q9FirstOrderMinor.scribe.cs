using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary;

internal sealed class Q9FirstOrderMinorDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9FirstOrderMinor";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A right kernel vector identifies the linear coefficient, and a left kernel vector can certify its nonvanishing.",
        H("First-order certificates for omitted-row minors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kernel-determinant-linear-coefficient"),
                DeclarationHandle.Create(Module + ".mul_coeff_one_det_pencil_eq_det_updateCol"),
                H("A right kernel vector identifies the determinant coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let A and E be square matrices on a finite index set over a commutative ring. If A x = 0, then for every column j, the j-th coordinate of x times the coefficient of X in det(A + X E) equals the determinant obtained from A by replacing column j by E x.")),
                    Paragraph(Text("Put M = A + X E over the polynomial ring. Replacing column j by M x multiplies its determinant by x(j), by the determinant law for a linear combination of columns. The kernel equation makes the new column X times E x. Pull out X from that column and compare coefficients of degree one. The constant coefficient on the replacement side is the determinant with the constant matrices, since taking constant coefficients is a ring homomorphism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("kernel-pairing-determinant-obstruction"),
                DeclarationHandle.Create(Module + ".coeff_one_det_pencil_ne_zero_of_pairing"),
                H("A nonzero left-right pairing certifies the minor"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Over a field, assume A x = 0, yᵀ A = 0, and yᵀ E x ≠ 0. If the columns of A other than j are linearly independent, then the coefficient of X in det(A + X E) is nonzero.")),
                    Paragraph(Text("A vector in the kernel of the replacement matrix gives a linear relation among its columns. Pairing with y forces the coefficient of column j to vanish. Independence forces the remaining coefficients to vanish. The replacement determinant is therefore nonzero, so the coefficient identity gives the claim."))),
                DescribeRole.Theorem),
            Paragraph(Text("For a rational weighted omitted-row matrix B(w), select a square submatrix of full column order and restrict it to the line w = w₀ + X h. Take A to be the chosen minor matrix at w₀ and E to be its perturbation in direction h. A nonzero pivot on the retained columns implies their independence in the chosen square submatrix. Right and left kernel vectors for A and a nonzero pairing with E then give a nonzero polynomial minor. Over the rationals this minor is nonzero at some rational point on the line because a nonzero polynomial has finitely many roots.")),
            Paragraph(Text("This criterion applies to each choice of rows and direction satisfying the certificate hypotheses. Hong, Wu and Xia's Problem 2 asks whether f₂(Q₉) equals 3 or 4. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
        []));
}
