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
                DescribeId.Create("strict-inventory-root-correction-statement"),
                DeclarationHandle.Create(Prefix + "strict_inventory_root_correction_statement"),
                H("Exact root-scale target proposition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This proposition is retained without a proof or freeze. The missing "
                        + "content is the uniform sqrt(2) second-layer cutoff, the o(sqrt(t)) "
                        + "all-layers-at-least-three tail, and the root-scale psi-theta limit."))),
                DescribeRole.Definition),
            Paragraph(Text(
                "The paper and theory attribution is the existing ZECKENDORF_EULER_5040 "
                + "Definition 7.1, Theorem 8.1 and equations (19)--(24), as cross-referenced "
                + "by the existing analytic workload note. The existing Lean O(sqrt(t)) "
                + "bound is not presented as this exact asymptotic."))));
}
