using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformHardCoreBaseLocusDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHardCoreBaseLocus";
    private const string Title = "The zero locus of periodic bond-two trace words";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorebaselocus-result"),
            DeclarationHandle.Create(Module + ".traceWord_zero_iff_baseInvariants"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every positive period, the full periodic trace-word tensor vanishes exactly on the listed trace-invariant locus. When at least one trace is nonzero, the three quadratic invariants are proportional to the corresponding trace products with coefficients fixed by a root of the power-trace polynomial. When both traces vanish, vanishing holds at odd periods and requires all three quadratic invariants to vanish at even periods."))),
            DescribeRole.Theorem))));
}
