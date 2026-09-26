using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics.DepthFirst;

internal sealed class DefaultDictionaryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/DagSemantics/DepthFirst/DefaultDictionary.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ConceptDynamics/zhao2023algorithm");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite dictionaries with a default",
        H("DefaultDictionary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("default-dictionary-update"),
                DeclarationHandle.Create(Prefix + "DefaultDict"),
                H("Finite dictionaries with a default"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The original interface specifies total lookup, finite support, a default value and point updates. The retained Vector.WithDefault instance supplies arbitrary finite index arrays."))),
                DescribeRole.Definition),
            Paragraph(Text("The immutable source mapping, modification notices, full Apache-2.0 license and replacement condition are in Library/ConceptDynamics/zhao2023algorithm.md. These statements concern Lean values and the DFS invariant; they do not establish C# execution, collection or parser correspondence, or physical stack bounds.")))));
}
