using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.MetallicHankel;

internal sealed class MetallicHankelBoundaryPolynomialsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/MetallicHankel/MetallicHankelBoundaryPolynomials.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/han2025hankel");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normal moment relations determine the complete supported Bezout formula for a Hankel inverse.",
        H("The Full Inverse at a Normal Hankel Index"),
        Blocks(
            Describe.Lean(DescribeId.Create("metallic-hankel-boundary-polynomials-hankel-inverse-bezout"),
                DeclarationHandle.Create(Prefix + "hankel_inverse_bezout"),
                H("Every inverse entry from the two normal polynomials"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Let mu be an integer moment sequence and N=n+1 be any positive size. Let c and d be integer coefficient sequences, extended by zero above degrees N and N-1 respectively, with c_N=1. Assume that c is orthogonal to moments at every shift t<N, and that the moment vector of d is minus the last basis vector: its moments vanish at t<N-1 and equal minus one at t=N-1. If H=(mu_(i+j)) has unit determinant, then its inverse entry at any i,j<N is minus the sum, over 0<=a<=j, of c_(i+j+1-a)d_a-d_(i+j+1-a)c_a. These are the coefficients of -(c(x)d(y)-d(x)c(y))/(x-y). The statement includes size one and imposes no condition on intervening principal minors.")),
                    Paragraph(Text("Multiplication by x modulo the monic polynomial c gives a companion matrix T. The normal moment relations give HT=T-transpose H and fix the last inverse column as -d. Symmetry fixes the last row. The resulting entry recurrence, descending in the row and ascending in the column, determines every inverse entry. Zero support at the last row supplies the boundary case of the finite sum. Thus the argument obtains the complete inverse even for a gapped normal family.")),
                    Paragraph(Text("For higher shifted metallic Hankel determinants, this identity supplies the inverse entries used in a fixed complementary minor of a larger normal matrix. MetallicHankelUnbounded.normal_family supplies these normal data at every prescribed period boundary. MetallicHankelComplementaryMinor consumes the inverse with exact ordered indices and signs, and MetallicHankelResiduePolynomials combines it with endpoint jets and backward integer-value propagation."))),
                DescribeRole.Theorem)
        ), []));
}
