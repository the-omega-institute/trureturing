using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.NumberTheory;

internal sealed class ProcyclicImageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Procyclic Image", H("Procyclic Image"),
        Blocks(
            Paragraph(Text("Compact subgroups of l-adic units (1 mod 4) are procyclic.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/NumberTheory/ProcyclicImage.exists_procyclic_generator"),
                H("exists_procyclic_generator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A continuous κ from a compact group to ℤ_ℓ^×, with values ≡ 1 mod 4 if ℓ = 2, has procyclic image: for some γ, every open subgroup containing γ and ker κ is the whole group.")))))));
}
