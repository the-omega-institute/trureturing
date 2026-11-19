using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class PosteriorCurvatureCostDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Convexity/PosteriorCurvatureCost.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal nonnegative posterior curvature integral is lower semicontinuous in the full weak topology of finite measures, with both infinite endpoint costs retained.",
        H("Posterior curvature and weak lower semicontinuity"), Blocks(
            Paragraph(Text("Let f be any real function convex on the positive real half-line. The curvature measure is the existing Stieltjes measure of its right derivative. No operator convexity or endpoint finiteness is required. For n in N, put a=1/(n+1), b=n+1. Integrate max(s v-u,0) on [a,1], and max(u-s v,0) on (1,b]. The atom at 1 belongs only to the first integral. These are finite real Bochner integrals because the curvature measure is finite on compact positive intervals.")),
            Node("curvatureTruncation", "Finite curvature truncations",
                "curvatureTruncation hf n u v is the sum of those two real integrals. The auxiliary positive endpoints small n, one and large n are defined inside the original Positive subtype.", false),
            Node("curvatureTruncation_nonneg", "Nonnegativity",
                "For every convexity witness hf, natural n and arbitrary real u,v, 0 <= curvatureTruncation hf n u v. Each hinge is nonnegative."),
            Node("curvatureTruncation_continuous", "Continuous in both real inputs",
                "For every hf and n the function (u,v) maps to curvatureTruncation hf n u v is continuous on R squared. The proof uses continuous parametric integration on the compact domains. The upper integral is expressed by restricting the curvature measure to (1,infinity), so its varying integrand is still integrated over a compact interval."),
            Node("curvatureTruncation_monotone", "Increasing truncations",
                "For every hf and real u,v, n maps to curvatureTruncation hf n u v is monotone. The lower domains increase as a decreases, the upper domains increase as b increases, and both integrands are nonnegative."),
            Node("iSup_curvatureTruncation", "Exact extended curvature remainder",
                "For every hf and arbitrary real u,v, the supremum over n of ENNReal.ofReal(curvatureTruncation hf n u v) equals the literal curvatureRemainder hf u v. The lower domains exhaust (0,1], the upper domains exhaust (1,infinity). Monotone convergence proves the equality with no finite-remainder premise, including infinite values at either posterior endpoint."),
            Node("posteriorTruncation", "Nonnegative continuous posterior functions",
                "Posterior is the compact interval [0,1]. posteriorTruncation hf n is the NNReal-valued continuous function t maps to curvatureTruncation hf n t (1-t), with its proved nonnegativity. The NNReal representation is a genuine continuous map.", false),
            Node("posteriorCurvatureCost", "The actual nonnegative weak-measure objective",
                "For every hf and nu in Mathlib's FiniteMeasure Posterior, posteriorCurvatureCost hf nu is the ENNReal lintegral of curvatureRemainder hf t (1-t) against nu. Its domain carries the stock topology of weak convergence of finite measures. The zero measure and arbitrary finite total mass are included.", false),
            Node("posteriorCurvatureCost_eq_iSup", "Exact increasing integral supremum",
                "For every hf and finite measure nu, posteriorCurvatureCost hf nu equals the supremum over n of the integral of posteriorTruncation hf n against nu, embedded in ENNReal. Pointwise exact exhaustion and monotone convergence in nu prove this equality. Infinity is preserved rather than truncated in the conclusion."),
            Node("posteriorCurvatureCost_lowerSemicontinuous", "Full weak lower semicontinuity",
                "For every hf, posteriorCurvatureCost hf is lower semicontinuous on FiniteMeasure Posterior. Each truncated integral is continuous by FiniteMeasure.continuous_lintegral_continuousMap; their exact supremum is lower semicontinuous. This uses the full weak topology and hence applies to arbitrary convergent nets. Only the curvature exhaustion is sequential; no sequential replacement of weak compactness or assumption of lower semicontinuity is used."),
            Paragraph(Text("These are scalar analytic suppliers for the arbitrary-von-Neumann original-source reverse-test problem. They reuse the repository's curvature representation and Mathlib's monotone convergence, continuous parametric integration and weak finite-measure topology. The truncation argument is standard measure theory; no literature novelty or independent attainment conclusion is claimed here. The consuming attainment module computes the original full objective as a fixed finite affine term plus this nonnegative extended integral."))
        )));

    private static DocumentBlock Node(string name, string title, string prose, bool theorem = true) =>
        Describe.Lean(DescribeId.Create("posteriorcurvaturecost-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
