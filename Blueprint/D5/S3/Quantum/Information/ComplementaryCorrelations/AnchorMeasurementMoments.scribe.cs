using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information.ComplementaryCorrelations;

internal sealed class AnchorMeasurementMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pauli and qutrit moments of centered scores.",
        H("Pauli and qutrit moments of centered scores"),
        Blocks(
            Describe.Lean(DescribeId.Create("qian-anchormeasurementmoments-pauli-midpoint"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementMoments.pauli_midpoint"),
                H("Centered Pauli midpoint entries"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The square root of a faithful qubit state gives explicit midpoint pairings between the centered X and Z observables."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-anchormeasurementmoments-simpson-gap-eq"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementMoments.simpson_gap_eq"),
                H("Reduction of the physical Simpson gap to scalar moments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The trace factors over the product state. The Pauli entries and qutrit centered moments give the scalar gap in Bloch coordinates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("qian-anchormeasurementmoments-bobr-observable-circulant"),
                DeclarationHandle.Create("D5/S3/Quantum/Information/ComplementaryCorrelations/AnchorMeasurementMoments.bobR_observable_circulant"),
                H("Fourier scores are circulant"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugating a real diagonal score by the qutrit Fourier unitary gives a Hermitian circulant observable."))), DescribeRole.Theorem))));
}
