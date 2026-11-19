using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class GaussianEntireEvaluationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/GaussianEntireEvaluation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Absolute summability and exact entire evaluation of the existing finite native Gaussian coefficients.",
        H("Native Gaussian entire evaluation"),
        Blocks(
            Paragraph(Text("Let I be any finite type, including the empty type, and E any complex matrix on I. Use the existing quadratic Q_E=(1/2)*sum_ij E_ij X_i X_j, Gaussian piece Q_E^n/n!, and native coefficient g_E(d) selected at n=degree(d)/2. No symmetry, positivity, spectral or contraction assumption is imposed. All products and transpose conventions are ordinary bilinear; no conjugation enters the quadratic.")),
            N("gaussianCoefficient_norm_summable", "Unrestricted absolute summability", "The full occupation family norm(g_E(d)) is summable. A private finite coefficient one-norm has triangle, scalar and finite-convolution multiplication bounds. Its value on Q_E is at most L=(1/2)*sum_ij norm(E_ij), so its value on Q_E^n/n! is at most L^n/n!. Homogeneity reduces every finite occupation subsum to finitely many pieces, and the real exponential series bounds that subsum by exp(L), independently of the chosen subset. Empty types and odd occupation degrees are covered by the same proof."),
            N("gaussianCoefficient_tsum", "Exact sum at the all-one assignment", "The unrestricted complex sum of g_E(d) equals Complex.exp((1/2)*sum_ij E_ij). At fixed d, homogeneity makes every piece coefficient vanish except possibly at degree(d)/2. Absolute summability of g_E therefore gives absolute summability on the product of piece degree and occupation. The two sums can be exchanged; the occupation sum of a polynomial is its evaluation at all variables equal to one, and the remaining degree sum is the ordinary complex exponential series."),
            Paragraph(Text("The finite one-norm proof adapts UniformCoefficientBudget's Causalean-derived polynomial argument to complex multivariate polynomials. Causalean is Copyright 2026 Jiyuan Tan, Apache-2.0, pinned at e56c1daecf6fc95cad721ff71d188e8fc526cbca. The existing license and notice are docs/reports/interpolation-suppliers/Causalean-LICENSE.txt and Causalean-NOTICE.txt. This is classical absolute power-series evaluation, with a new native coefficient implementation rather than a literature novelty claim.")),
            Paragraph(Text("This theorem supplies the future outer auxiliary Gaussian sum after finite affine sewing. It does not prove the affine factorial-l2 majorant, joint internal/auxiliary summability, original identityK or C1, a source identification, physical realization, or the full string/AdS-CFT objective. Those remain separate obligations."))),
        []));

    private static DocumentBlock N(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("gaussian-entire-evaluation-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
