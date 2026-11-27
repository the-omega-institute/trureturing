using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Algebra;

internal sealed class TangentNakayamaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Tangent Nakayama", H("Tangent Nakayama"),
        Blocks(
            Paragraph(Text("General lemmas of commutative and general algebra (textbook or folklore).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Algebra/TangentNakayama.exists_mem_colon_of_tangent"),
                H("exists_mem_colon_of_tangent"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Nakayama in tangent form: let x : S → V be a section of a finite type V-algebra, φ : V → k a field point, I ⊆ ker x. If every k[ε]-point over φ lifting φ∘x that kills I kills ker x, some b with b·ker x ⊆ I has φ(x(b)) ≠ 0.")))))));
}
