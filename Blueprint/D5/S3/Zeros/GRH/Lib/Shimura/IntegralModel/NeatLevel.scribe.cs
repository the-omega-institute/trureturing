using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.IntegralModel;

internal sealed class NeatLevelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Neat Level", H("Neat Level"),
        Blocks(
            Paragraph(Text("Marked triples, orbital counts, local embeddings, Hecke operators at split places, local terms. Frames determine forms, automorphisms are similitudes, levels of large norm are neat.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/IntegralModel/NeatLevel.classAut_eq_bot"),
                H("classAut_eq_bot"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Neatness, for E with at least two infinite places: let w_i be distinct finite places with (2n)^[E:ℚ] < ∏ q_{w_i}, and K ⊂ G_f ∩ GL_n(Ô) a subgroup reducing to 1 modulo every w_i. Then Γ_f ∩ gKg⁻¹ is trivial for all g, Γ_f the rational unitary group of the definite space I_n.")))))));
}
