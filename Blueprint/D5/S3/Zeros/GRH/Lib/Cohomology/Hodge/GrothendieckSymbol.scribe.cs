using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Hodge;

internal sealed class GrothendieckSymbolDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Grothendieck Symbol", H("Grothendieck Symbol"),
        Blocks(
            Paragraph(Text("Grothendieck symbols [dT/T]: definition, transformation law, multiplicativity, degree-one form.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/GrothendieckSymbol.symbolClass_succ"),
                H("symbolClass_succ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("In characteristic 0: under 𝔸^d × 𝔸^1 → 𝔸^{d+1}, which respects the complements of the origin, the class [dT/T] of degree d + 1 pulls back to the external product of the classes [dT/T] of degrees d and 1.")))))));
}
