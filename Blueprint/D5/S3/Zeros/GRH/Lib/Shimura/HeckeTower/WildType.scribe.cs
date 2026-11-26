using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.HeckeTower;

internal sealed class WildTypeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Wild Type", H("Wild Type"),
        Blocks(
            Paragraph(Text("Local GL_n at split places, spherical Hecke elements, commuting operators on base cohomology. Existence of a wild supercuspidal-type character; principal level inside an open subgroup.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/HeckeTower/WildType.exists_levelGU_conj_le"),
                H("exists_levelGU_conj_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let the open H contain the integral points trivial at S, each w in S having w or w̄ in B. Then some multiple 𝔑 of N in O_E lies exactly in the primes of B and those containing N, and u ∈ H whenever ū has principal level 𝔑.")))))));
}
