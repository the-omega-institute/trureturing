using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCoreTransferRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCoreTransferRecurrence";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Length recurrences for raw transfer coefficients",
        H("Length recurrences for raw transfer coefficients"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcoretransferrecurrence-hardcoreraw-fibonacci-iff-initial"),
                DeclarationHandle.Create(Module + ".hardCoreRaw_fibonacci_iff_initial"),
                H("From finitely many initial lengths to all lengths"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For degree r ≤ 4, the binary bond-two raw transfer coefficient at the hard-core base and a candidate formed from two Fibonacci sequences with weights of degree at most r satisfy the same recurrence in length. Its characteristic polynomial is (X² − X − 1)^(r+1). Equality for lengths n ≥ 7 is therefore equivalent to equality on the first 2(r+1) lengths starting at seven."))),
                DescribeRole.Theorem))));
}
