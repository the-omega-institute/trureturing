using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class LevelPlacesChosenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Level Places Chosen", H("Level Places Chosen"),
        Blocks(
            Paragraph(Text("Avatars of algebraic characters: conjugate duality, inertia action; names for Galois group and places. Apt tuples sit at chosen places; distinct N-th roots of unity in ℚ̄_ℓ are at least ‖N‖ apart.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/LevelPlacesChosen.isLabelledAt_avatar"),
                H("isLabelledAt_avatar"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let w be split, A a place over w, and the tame part ψ of a trivial at w̄. Then inertia at A acts on the avatar of bc(a)·υ^{−k}·|·|^{j−k/2} through the tame character given by the label of ψ_w.")))))));
}
