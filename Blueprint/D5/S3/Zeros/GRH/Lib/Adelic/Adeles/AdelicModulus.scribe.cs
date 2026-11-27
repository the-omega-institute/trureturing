using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Adeles;

internal sealed class AdelicModulusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adelic Modulus", H("Adelic Modulus"),
        Blocks(
            Paragraph(Text("Haar modulus of ideles and adelic matrices is the adelic absolute value.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Adeles/AdelicModulus.volume_map_mul_mul_adele"),
                H("volume_map_mul_mul_adele"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a in GL_n(𝔸) and b in GL_1(𝔸), the map x ↦ axb on n×1 adelic matrices pushes the standard measure forward to |det(b)^n det a|⁻¹ times itself, with |·| the module of an idele.")))))));
}
