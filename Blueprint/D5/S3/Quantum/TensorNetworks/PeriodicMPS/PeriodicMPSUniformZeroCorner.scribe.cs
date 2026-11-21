using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformZeroCornerDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformZeroCorner";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The vanishing adjacent-ones population",
        H("The vanishing adjacent-ones population"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformzerocorner-trace-det-sq-second-eq-zero-of-rawtwo-corner-zero"),
                DeclarationHandle.Create(Module + ".trace_det_sq_second_eq_zero_of_rawTwo_corner_zero"),
                H("A square-zero occupied core"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a nonzero periodic binary bond-two trace tensor at length at least four, vanishing of the raw 11,11 population forces zero trace, zero determinant and square zero for the occupied core. The corner is a sum of squared moduli, so every trace word starting in 11 vanishes. Comparing these vanishing traces with traces of powers, and using the two-by-two Cayley–Hamilton identity, gives the restrictions on the core."))),
                DescribeRole.Theorem))));
}
