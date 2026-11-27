using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class ReducedClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduced Closure", H("Reduced Closure"),
        Blocks(
            Paragraph(Text("Line bundles as cocycles of functions on ring-valued points; sections, frames. Dense complex points, reduced closure, lifting maps into closed subschemes.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/ReducedClosure.exists_reduced_closure"),
                H("exists_reduced_closure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Reduced closure: complex points ξ_z : Spec ℂ → X factor as ξ_z = i ∘ e_z through a closed immersion i : Y → X, with Y reduced and the points e_z dense in Y.")))))));
}
