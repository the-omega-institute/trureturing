using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.TraceFormula;

internal sealed class ChangingSignsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Changing Signs", H("Changing Signs"),
        Blocks(
            Paragraph(Text("Finitely many double cosets of frames of given signature (finite class number). Changing real signs of elliptic classes by a global element locally a norm.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/TraceFormula/ChangingSigns.exists_hasSignType_mul_iff"),
                H("exists_hasSignType_mul_iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Change of signs. If each η_μ has product 1, some permutation of the GL_n(E)-orbits of triples has the form (q, y, μ) ↦ (Uq, y, μ), where U ∈ GL_n(𝔸_f) depends on y, μ only, commutes with the centraliser of y in GL_n(E), and (x, y) has type εη_μ iff (Ux, y) has type ε.")))))));
}
