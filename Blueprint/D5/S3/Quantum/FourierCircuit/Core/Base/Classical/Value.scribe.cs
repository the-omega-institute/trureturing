using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Classical;

internal sealed class ValueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Classical Value", H("Core Base Classical Value"), Blocks(
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Value.Value"),
                H("Value"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Nominal runtime encodings carried by the closed storage shapes. Every constructor fixes its CShape index, so equal-width unsigned, signed, residue, unit-residue, bit-vector, and fixed-vector values remain distinct types. Residue and elliptic-curve constructors are raw encodings only: their modulus, unit, curve, and validity proofs belong to later semantic carriers."))), DescribeRole.Definition))));
}
