using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Orthogonality;
internal sealed class CompatibleFamilyCheckDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original seven-dimensional written lower-bound proof.",
        H("CompatibleFamilyCheck"),
        Blocks(Describe.Lean(DescribeId.Create("law-0"), DeclarationHandle.Create("D5/S3/Combinatorics/Orthogonality/CompatibleFamilyCheck.sound"), H("sound"), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/QuadraticForms/binarysubspace2026complete")), Blocks(Paragraph(Text("The terminating include/omit recurrence checks every compatible extension, including empty and nonmaximal classes. The proof establishes soundness for arbitrary element types, original predicates and bounded candidate lists. The full126-minimum instance supplies all actual data and uses the resulting class property in the written graph obstruction."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/Orthogonality/WeightedIndependentBound"))]));
}
