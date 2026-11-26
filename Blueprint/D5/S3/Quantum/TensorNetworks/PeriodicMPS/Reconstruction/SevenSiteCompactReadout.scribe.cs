using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteCompactReadoutDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCompactReadout";
    private const string Title = "Pauli coordinates for exchange-symmetric two-site densities";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("sevensitecompactreadout-result"),
            DeclarationHandle.Create(Module + ".eq_of_readout_of_trace_eq"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Two Hermitian exchange-symmetric two-qubit matrices with equal real traces and equal values of the nine selected real Pauli readings are equal. Exchange supplies the readings with the factors in the swapped order, and the trace supplies the identity-pair reading.")),
                Paragraph(Text("For projectors in the compact closure of actual periodic binary bond-two states, the adjacent marginal is Hermitian, exchange symmetric and trace one. On this source, equality of the nine readings is equivalent to equality of the literal marginal."))),
            DescribeRole.Theorem))));
}
