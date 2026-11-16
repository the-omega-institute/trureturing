using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Classical;

internal sealed class OracleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Classical Oracle", H("Core Base Classical Oracle"), Blocks(
            Describe.Lean(DescribeId.Create("instance-coordinatedecidableeq"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Oracle.coordinateDecidableEq"),
                H("coordinateDecidableEq"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("For every classical oracle model, this instance supplies decidable equality on its accounting coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Oracle.ClassicalOracleModel"),
                H("ClassicalOracleModel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Fixed query interfaces with structural separation of independent services."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Classical/Oracle.Coordinate"),
                H("Coordinate"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Native coordinates retain the originating service."))), DescribeRole.Definition))));
}
