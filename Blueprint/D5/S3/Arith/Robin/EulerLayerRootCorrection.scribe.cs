using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class EulerLayerRootCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/EulerLayerRootCorrection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact strict Euler inventory root correction is retained as an open proposition.",
        H("Strict Euler Inventory Root Correction"),
        Blocks(
            Paragraph(Text(
                "For every positive epsilon, the target asks for one real threshold T>1 "
                + "that works for every real t>=T and every positive natural U satisfying "
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
                DescribeId.Create("strict-inventory-root-correction-statement"),
                DeclarationHandle.Create(Prefix + "strict_inventory_root_correction_statement"),
                H("Exact root-scale target proposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This proposition is retained without a proof or freeze. The missing "
                        + "content is the uniform sqrt(2) second-layer cutoff, its weighted "
                        + "prime-mass asymptotic, and the root-scale psi-theta limit. The "
                        + "third-and-higher tail is now supplied separately by the two "
                        + "consumed declarations above."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "The paper and theory attribution is the existing ZECKENDORF_EULER_5040 "
                + "Definition 7.1, Theorem 8.1 and equations (19)--(24), as cross-referenced "
                + "by the existing analytic workload note. The existing Lean O(sqrt(t)) "
                + "bound is not presented as this exact asymptotic. The faithful Reg "
                + "source reconstruction remains open and does not claim a validated "
                + "four-slot registration."))));
}
