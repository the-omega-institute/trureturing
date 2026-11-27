using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.Holomorphic;

internal sealed class HolomorphicMinorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Holomorphic Minor", H("Holomorphic Minor"),
        Blocks(
            Paragraph(Text("Highest coefficient is holomorphic; circle mean and reproducing property of holomorphic functions.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/Holomorphic/HolomorphicMinor.eq_holMinorsPi_mul"),
                H("eq_holMinorsPi_mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let the order o be injective with signs +1 first, each u_τ K-dominant, and F holomorphic of weight u on U(diag ε)^Φ with F(g⁻¹) = conj F(g). Then F = F(1)·holMinorsPi ε u.")))))));
}
