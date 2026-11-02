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
            Node("1", "euler_coefficient_finite", "The supplied Euler construction agrees with every sufficiently long finite product, not just with a chosen numerical truncation.", DescribeRole.Theorem),
            Node("2", "finiteEulerEvaluation", "Evaluation in the Laurent variable is performed only on finite polynomials. The growing cutoff is subsequently justified coefficientwise.", DescribeRole.Definition),
            Node("3", "finiteEulerEvaluation_eq_prod", "The finite polynomial evaluation is exactly its finite product of linear factors.", DescribeRole.Theorem),
            Node("4", "eulerEvaluation", "The coefficientwise stabilized Euler evaluation.", DescribeRole.Definition),
            Node("5", "tendsto_finiteEulerEvaluation", "The formal Euler evaluation is the coefficientwise limit of its actual finite products. No unrestricted power-series substitution is used.", DescribeRole.Theorem),
            Node("6", "formalTheta_eq_eulerEvaluations", "The actual Laurent product supplier equals two separately justified Euler evaluations.", DescribeRole.Theorem),
            Node("7", "jacobiSeries", "The Jacobi series is normalized by the actual pentagonal Euler product.", DescribeRole.Definition),
            Node("8", "tendsto_finite_jacobi", "The normalized Laurent series is a limit of the actual three Jacobi factors.", DescribeRole.Theorem),
            Node("9", "jacobiSeries_column", "Every Laurent column of the actual product is the corresponding single Jacobi monomial.", DescribeRole.Theorem),
            Node("extra-0", "tendsto_finite_jacobi_successor", "Keeping one additional zero-shift factor has the same genuine Jacobi limit.", DescribeRole.Theorem),
            Paragraph(Text("This is classical intermediate mathematics. CubicThetaCoreProduct supplies the downstream product-to-core lattice identity and EtaSignK6 supplies the exact all-index sign theorem. Independent formal acceptance and publication remain separate; no literature priority or novelty credit is asserted."))
        ), []));

    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-jacobi-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
