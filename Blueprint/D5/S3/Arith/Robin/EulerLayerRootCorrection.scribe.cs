using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class EulerLayerRootCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/EulerLayerRootCorrection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict Euler inventory has uniform root correction sqrt(2)-1.",
        H("Strict Euler Inventory Root Correction"),
        Blocks(
            Paragraph(Text(
                "For every positive epsilon, one real threshold T>1 "
                + "works for every real t>=T and every positive natural U satisfying "
                + "the literal strict prime factorization law, with "
                + "|(log U-psi(t))/sqrt(t)-(sqrt(2)-1)|<epsilon. Equality layers remain excluded.")),
            Describe.Lean(
                DescribeId.Create("strict-inventory-third-layer-bound"),
                DeclarationHandle.Create(Prefix + "strict_inventory_third_layer_bound"),
                H("Finite envelope for the complete third-and-higher layer mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real t>=2 and every positive natural U satisfying "
                        + "the literal strict factorization law, the sum of "
                        + "(factorization(q)-2)*log(q) over prime factors with "
                        + "factorization(q)>=3 is at most "
                        + "((3*t)^(1/3)+1)*log(t*log(t)/log(2)). The proof uses "
                        + "the actual active-power cutoff and a finite support count; "
                        + "all active exponent layers remain in the mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-inventory-third-layer-vanishing"),
                DeclarationHandle.Create(Prefix + "strict_inventory_third_layer_vanishing"),
                H("Uniform root-scale vanishing of layers at least three"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive epsilon there is one threshold T>1 "
                        + "such that every real t>=T and every positive strict "
                        + "inventory integer U have third-and-higher layer mass "
                        + "divided by sqrt(t) below epsilon. An explicit "
                        + "240*t^(-7/60) envelope proves the uniform limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-inventory-second-layer-limit"),
                DeclarationHandle.Create(Prefix + "strict_inventory_second_layer_limit"),
                H("Uniform second-layer mass coefficient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The literal sum of log(q) over prime factors with exponent at least "
                    + "two, divided by sqrt(t), tends uniformly to sqrt(2). For every "
                    + "0<c<sqrt(2), all primes q<=c*sqrt(t) are strictly active beyond "
                    + "one common threshold: the logarithmic marginal is bounded below "
                    + "using 1/(q^2+q+1). Actual active squares satisfy q^2<2*t. "
                    + "Unconditional PNT squeezes the weighted mass between the two "
                    + "theta functions. Equality events are included in t and excluded "
                    + "from the active layers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-inventory-root-correction-statement"),
                DeclarationHandle.Create(Prefix + "strict_inventory_root_correction_statement"),
                H("Exact root-scale statement"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The statement keeps all real parameters, all prime factorization "
                        + "equalities and all positive natural inventory integers. The "
                        + "following theorem proves this exact proposition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("strict-inventory-root-correction"),
                DeclarationHandle.Create(Prefix + "strict_inventory_root_correction"),
                H("Uniform strict inventory root correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof splits log(U) into first, second and all remaining "
                    + "layers. The first-layer error is bounded by log(t), the second "
                    + "layer contributes sqrt(2)*sqrt(t), and the entire higher tail "
                    + "is o(sqrt(t)). Costa-Pereira bounds and the existing unconditional "
                    + "MediumPNT give (psi(t)-theta(t))/sqrt(t)->1. Combining the four "
                    + "errors gives the exact uniform coefficient sqrt(2)-1. This is "
                    + "an arithmetic supplier for the Robin/5040 program, and does "
                    + "not prove RH or a signed-tail or attainment statement."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The paper and theory attribution is the existing ZECKENDORF_EULER_5040 "
                + "Definition 7.1, Theorem 8.1 and equations (19)--(24), as cross-referenced "
                + "by the existing analytic workload note. The existing Lean O(sqrt(t)) "
                + "bound is not presented as this exact asymptotic. The outer Reg "
                + "source binding remains unfinished and does not claim a validated "
                + "four-slot registration.")))));
}
