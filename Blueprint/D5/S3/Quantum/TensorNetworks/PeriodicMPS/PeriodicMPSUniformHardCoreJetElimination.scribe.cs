using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreJetEliminationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreJetElimination";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Elimination in the normalized hard-core jet",
        H("Elimination in the normalized hard-core jet"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorejetelimination-fold-slopes"),
                DeclarationHandle.Create(Module + ".fold_slopes"),
                H("The two slopes permitted by matching coherence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Under the displayed nonzero conditions, solving the regular quadratic equations factors the coherence difference. Vanishing of that difference forces the reference slope one or the second root given by the ratio of the fold coefficients."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorejetelimination-quartic-difference"),
                DeclarationHandle.Create(Module + ".quartic_difference"),
                H("The residual quartic after eliminating regular rows"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("At the second root, the specified cubic regular-row relation accounts for a reparameterization term. Subtracting its quartic contribution to the forbidden population yields the explicit rational expression in length and the Fibonacci ratio."))),
                DescribeRole.Theorem))));
}
