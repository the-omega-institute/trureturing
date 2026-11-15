using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class NormalOverlapCurvatureEqualityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/NormalOverlapCurvatureEquality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal closed-curvature profiles of actual normal overlaps and sufficiency of finite compatibility for the original standard-source maximal value.",
        H("Literal closed-curvature profiles of actual normal overlaps and sufficiency of finite compatibility for the original standard-source maximal value"), Blocks(
            Node("family_hinge_integrals", "Exact two hinge profiles", "For every actual family and every real t, the two nonnegative ENNReal hinge integrals equal ofReal(t sigma(1)-overlap(F,t)(1)) and ofReal(rho(1)-overlap(F,t)(1)). Continuous functions on the closed posterior interval are integrable; scalar min identities, both exact moments and the complex mass identity prove the result. Both axes and unnormalized masses remain included.", true),
            Node("familyCost_eq_overlap_curvature", "Closed cost from actual overlaps", "The literal closedPerspectiveCost of EVERY actual posterior family is its fixed finite affine contribution plus the lower and upper curvature integrals of its actual overlap mass deficits. The original endpoint-inclusive scalar curvature identity and nonnegative Tonelli theorem supply the full remainder, including infinite endpoints and infinite costs. The whole atom at one belongs to the lower branch Iic 1.", true),
            Node("maximalValue", "Literal standard-original maximal infimum", "Take sInf of standardAttainableCosts in the independently fixed source universe u, with arbitrary concrete Hilbert-space universe v. This is the original sigma-finite source class with positive algebraic complex-linear preparations on the entire complex L1 and independently defined coefficient-series outputs. No optimizer or chosen-test finite-cost condition changes this class.", false),
            Node("hockeyValue", "Optimal-overlap curvature formula", "This definition is the finite affine term plus the two ENNReal curvature integrals of the actual normal-overlap maximum deficits. The atom at one is in Iic 1. Identification with the original operational single-hinge reverse-test infima requires its own source-equivalence proof; the definition does not assert that identification.", false),
            Node("finite_compatibility_implies_original_equality", "Finite compatibility yields original maximal attainment", "FiniteCompatibility on the support of the actual positive-ray curvature measure yields equality between the literal standard-original maximal infimum and hockeyValue, and an actual posterior family whose literal closed cost attains that value and every support overlap optimum. The proof uses the full original cost-set equality, never an infimum-integral interchange. The curvature measure is concentrated on its support; pointwise optimality there gives equality of the complete endpoint-inclusive nonnegative integrals. The comparison in the other direction follows for every actual source from its posterior family. This sufficiency statement permits infinite values and makes no necessity assertion for infinity=infinity. The separate operational single-hinge identification remains outside this declaration.", true),
            Paragraph(Text("The mathematical source is the earlier arbitrary-curvature finite-compatibility manuscript and its independent review. Hiai--Mosonyi--Tomamichel, Hockey stick f-divergences, arXiv:2607.08760v1, supplies the original reverse-test and curvature framework and leaves the maximal-hockey equality classification open on PDF p. 62. The functional-analytic and scalar curvature ingredients are established antecedents. This source makes no worldwide-priority or model-diversity claim and does not include the separate full-support localized-centralizer theorem."))
        )));

    private static DocumentBlock Node(string name, string title, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("normaloverlapcurvatureequality-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
