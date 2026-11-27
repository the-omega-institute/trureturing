using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Hodge;

internal sealed class WitnessCocyclesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Witness Cocycles", H("Witness Cocycles"),
        Blocks(
            Paragraph(Text("Class of the diagonal and Künneth surjectivity in Hodge cohomology (Grothendieck symbols) (known result; see Lib.Cohomology.Hodge.FixedPointFormula).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/WitnessCocycles.exists_map_extClass_comp"),
                H("exists_map_extClass_comp"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let γ: S₂ → T₂, y: S₃ → T₃ be compatible maps between short exact sequences S, T, and β: T₁ → F. Some z: S₁ → F has z(s) = β(t) whenever t and s have matching images in T₂, and y^*β_*[T] = z_*[S] in Ext¹(S₃, F).")))))));
}
