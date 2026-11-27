using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Groups;

internal sealed class CentralProjectionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Central Projections", H("Central Projections"),
        Blocks(
            Paragraph(Text("Central idempotents of group algebras and their tensor products over product groups.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Groups/CentralProjections.asAlgebraHom_piTensorElem_mulSingle"),
                H("asAlgebraHom_piTensorElem_mulSingle"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a complex representation ρ of a finite product ∏ G_j of finite groups and x in ℂ[G_i], the pure tensor with x at i and 1 elsewhere acts as x acts in the restriction of ρ to the factor G_i.")))))));
}
