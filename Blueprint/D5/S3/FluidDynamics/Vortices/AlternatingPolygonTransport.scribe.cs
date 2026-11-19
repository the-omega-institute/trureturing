using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Vortices;

internal sealed class AlternatingPolygonTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Vortices/AlternatingPolygonTransport.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/FluidDynamics/barrykevrekidis2013vortex");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The parameter operator is the complexification of the actual field derivative at the physical radius. Differentiated field scaling identifies it with 2*Omega times the normalized derivative. Every level of every generalized eigenspace is preserved under the corresponding eigenvalue scaling. The characteristic polynomial identity and rescaled neutral chain record the full Jordan transport.",
        H("Alternating Polygon Transport"), Blocks(
            Paragraph(Text("The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.")),
            Node("parameter_matrix_eq", "Actual physical matrix equality", "Differentiate the physical field scaling and map the actual real Cartesian derivative into the complex numbers. This is the matrix identity used by both the operator and characteristic-polynomial transport.", DescribeRole.Theorem),
            Node("smul_genEigenspace", "smul genEigenspace", "Scalar dilation preserves every level of the generalized-eigenspace filtration.", DescribeRole.Theorem),
            Node("charpoly_smul_eval", "charpoly smul eval", "Determinant scaling, including the zero characteristic root.", DescribeRole.Theorem),
            Node("charpoly_smul_polynomial", "charpoly smul polynomial", "Polynomial, rather than root-list, scaling of an actual square matrix.", DescribeRole.Theorem),
            Node("parameterOperator", "parameterOperator", "The physical derivative at the radius selected by b and Omega.", DescribeRole.Definition),
            Node("parameterOperator_eq", "parameterOperator eq", "The actual complexified physical derivative is exactly 2*Omega times the normalized actual operator.", DescribeRole.Theorem),
            Node("parameter_genEigenspace", "parameter genEigenspace", "Every eigenvalue and every Jordan filtration level transports from the actual field.", DescribeRole.Theorem),
            Node("parameter_charpoly", "parameter charpoly", "As a polynomial, the actual physical characteristic polynomial is a to the 4m times chi(lambda/a), where a=2*Omega.", DescribeRole.Theorem),
            Node("parameter_neutral_chain", "parameter neutral chain", "The chain length stays two; only the generalized vector is rescaled.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("alternating-polygon-transport-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
}
