using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.NumberTheory;

internal sealed class ClassNumberBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Class Number Bound", H("Class Number Bound"),
        Blocks(
            Paragraph(Text("Crude bound for the class number by degree and discriminant.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/NumberTheory/ClassNumberBound.classNumber_le"),
                H("classNumber_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The class number of a number field F of degree n over ℚ is at most (2ⁿ |disc F|)^{n+1}.")))))));
}
