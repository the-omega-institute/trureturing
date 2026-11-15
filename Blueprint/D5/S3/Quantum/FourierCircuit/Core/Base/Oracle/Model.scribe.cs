using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.FourierCircuit.Core.Base.Oracle;

internal sealed class ModelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Addressed quantum circuit: Core Base Oracle Model", H("Core Base Oracle Model"), Blocks(
            Paragraph(Text("For every OracleModel model, Occurrence query and Interpretation environment, QuantumAlg.OracleModel.Occurrence.coordinate query is model.coordinate query.query. Its operator reindexes environment.operator query.query along the certified placement index equivalence.")),
            Describe.Lean(DescribeId.Create("declaration0"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Oracle/Model.OracleModel"),
                H("OracleModel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("A declaration of available unitary queries with their own accounting coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration1"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Oracle/Model.Interpretation"),
                H("Interpretation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("A mathematical interpretation of the granted queries, supplied only at execution."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration2"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Oracle/Model.empty"),
                H("empty"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("The absence of oracle access has no query instances and no query coordinates."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration3"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Oracle/Model.emptyInterpretation"),
                H("emptyInterpretation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("Empty access has one interpretation and cannot reveal any oracle information."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("declaration4"),
                DeclarationHandle.Create("D5/S3/Quantum/FourierCircuit/Core/Base/Oracle/Model.Occurrence"),
                H("Occurrence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Fourier/qudeleap2026qft")),
                Blocks(Paragraph(Text("One granted query, placed on systems of exactly its declared dimensions."))), DescribeRole.Definition))));
}
