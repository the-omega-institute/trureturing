using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.Crystalline;

internal sealed class CrystallineEtaleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crystalline Etale", H("Crystalline Etale"),
        Blocks(
            Paragraph(Text("A_max as Frobenius-twisted A_inf-algebra; map from O_C to A_max modulo divided powers. Étale algebras lift along surjections; étale over perfect is perfect. Crystalline comparison is bijective on algebras etale over a perfectoid torus.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/Crystalline/CrystallineEtale.hasCrysComparison_of_etale"),
                H("hasCrysComparison_of_etale"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If G is a commutative monoid that is a module over ℚ≥0 and B is étale over the monoid algebra O_C[G], then the crystalline comparison is bijective (HasCrysComparison) for the functor Hom(B, −) on O_C-algebras.")))))));
}
