using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class EulerLayerRootSecondOrderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/EulerLayerRootSecondOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict Euler inventory has a uniform next logarithmic root coefficient.",
        H("Strict Euler Inventory Second-Order Root Correction"),
        Blocks(
            Paragraph(Text(
                "For every positive real epsilon there is one real threshold T>1 such that, "
                + "for every real t>=T and every positive natural U satisfying the exact "
                + "strict prime factorization law at 1/(t*log(t)), the normalized root "
                + "correction has the next coefficient.")),
            Describe.Lean(
                DescribeId.Create("strict-inventory-root-second-order"),
                DeclarationHandle.Create(Prefix + "strict_inventory_root_second_order"),
                H("Uniform second-order strict inventory law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The conclusion retains every real clock, every prime binder, "
                        + "the strict optimalLayerCount equality, and every positive natural "
                        + "inventory witness. It asserts "
                        + "abs(log(t)*((log(U)-psi(t))/sqrt(t)-(sqrt(2)-1)) "
                        + "+sqrt(2)*log(2)/2)<epsilon.")),
                    Paragraph(Text(
                        "The proof reuses the existing MediumPNT and the first-layer and "
                        + "third-layer inventory bounds. The second layer is bracketed between "
                        + "theta(rho-1) and theta(rho), where rho is the unique real solution "
                        + "of rho^2*log(rho)=t*log(t). Writing "
                        + "s=rho/sqrt(2*t) and using the exact equation gives "
                        + "log(t)*(s-1) tending to -log(2)/2 without assuming an expansion. "
                        + "The resulting coefficient is -sqrt(2)*log(2)/2.")),
                    Paragraph(Text(
                        "The one-unit bracket contains equality events and contributes only "
                        + "O(log(rho)). The prime-power terms above the square layer and the "
                        + "third-and-higher actual inventory are retained in the remainder at "
                        + "the smaller sqrt(t)/log(t) scale. No RH, JY, signed-tail, Robin, "
                        + "or attainment assertion is included."))),
                DescribeRole.Theorem))));
}
