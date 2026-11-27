using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.Places;

internal sealed class ProfiniteGaloisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Profinite Galois", H("Profinite Galois"),
        Blocks(
            Paragraph(Text("Infinite Galois theory for an abstract profinite group: fixed fields, restriction, continuity.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/Places/ProfiniteGalois.fixingSubgroup_fixedFieldOf"),
                H("fixingSubgroup_fixedFieldOf"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Galois correspondence: a closed subgroup H of the Galois group Γ of Ω/K is the subgroup fixing the fixed field of H.")))))));
}
