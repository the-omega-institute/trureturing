using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Primitives.QFT.Mathematics;

internal sealed class PhaseFactorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Primitives QFT Mathematics PhaseFactors", H("Primitives QFT Mathematics PhaseFactors"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseAngle"),
                H("qftPhaseAngle"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Rotation angle used between the leading wire and the (offset+1)st wire of one recursive QFT stage."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactorPrefix"),
                H("qftPhaseLayerFactorPrefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Scalar accumulated by the first count controlled phases of one QFT stage on a computational-basis label."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseFactorAt"),
                H("qftPhaseFactorAt"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("One phase-layer factor, indexed in source-circuit order."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.natOfBits_eq_sum"),
                H("natOfBits eq sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Reconstruct a natural number as the weighted sum of its finite bit vector."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactorPrefix_eq_prod"),
                H("qftPhaseLayerFactorPrefix eq prod"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The recursive scalar accumulator is exactly the product of the phase factors represented by its first count structural leaves."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration5"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseAngle_exp_eq_omega_pow"),
                H("qftPhaseAngle exp eq omega pow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The source angle of one phase leaf is the corresponding binary-weight power of the common (n+1)-qubit Fourier root."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration6"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseFactorAt_eq_omega_pow"),
                H("qftPhaseFactorAt eq omega pow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Each actual controlled-phase leaf contributes the Fourier-root power of its addressed input bit, and contributes one when the leading bit is zero."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("declaration7"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Primitives/QFT/Mathematics/PhaseFactors.qftPhaseLayerFactor_eq"),
                H("qftPhaseLayerFactor eq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The complete phase layer contributes the Fourier root raised to the lower n input bits whenever the leading output branch is one."))), DescribeRole.Lemma))));
}
