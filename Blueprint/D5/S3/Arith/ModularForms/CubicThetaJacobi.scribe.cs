using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaJacobiEncodedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaJacobi.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual finite Jacobi products and their Laurent columns", H("Actual finite Jacobi products and their Laurent columns"), Blocks(
            Paragraph(Text("The existing InversionSeq207 Euler and Durfee triple-product proof supplies the algebraic coefficients. This module proves finite-product stabilization and justifies the special evaluations coefficientwise; it assumes no cubic theta identity.")),
            Node("0", "finiteEulerPolynomial", "Actual finite Euler polynomial in a separate polynomial variable.", DescribeRole.Definition),
            Node("1", "euler_coefficient_finite", "Every coefficient of the supplied Euler construction agrees with every sufficiently long actual finite product.", DescribeRole.Theorem),
            Node("2", "finiteEulerEvaluation", "A polynomial evaluation at a Laurent coefficient times a nonnegative power of X.", DescribeRole.Definition),
            Node("3", "finiteEulerEvaluation_eq_prod", "The finite polynomial evaluation is exactly its finite product of linear factors.", DescribeRole.Theorem),
            Node("4", "eulerEvaluation", "The coefficientwise stabilized Euler evaluation.", DescribeRole.Definition),
            Node("5", "tendsto_finiteEulerEvaluation", "The genuine finite products converge to the evaluation at every nonnegative shift.", DescribeRole.Theorem),
            Node("6", "formalTheta_eq_eulerEvaluations", "The supplied Laurent product is the product of the two separately justified evaluations.", DescribeRole.Theorem),
            Node("7", "jacobiSeries", "The supplied formalTheta normalized by the actual pentagonal Euler series.", DescribeRole.Definition),
            Node("8", "tendsto_finite_jacobi", "The actual three Jacobi product factors converge to jacobiSeries.", DescribeRole.Theorem),
            Node("9", "jacobiSeries_column", "Every integer Laurent column is the exact signed triangular Jacobi monomial, by the repository supplier.", DescribeRole.Theorem),
            Paragraph(Text("This is classical intermediate mathematics. The product-to-core lattice identity and the complete original k6 sign theorem are separate remaining obligations; no original-problem completion or novelty credit is asserted."))
        ), []));

    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-jacobi-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
