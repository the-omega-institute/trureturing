using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.ClassField.GreenbergWiles;

internal sealed class ProjectiveCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projective Count", H("Projective Count"),
        Blocks(
            Paragraph(Text("Count of trivialised cocycles for a projective module (Euler characteristic type formula).")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/ClassField/GreenbergWiles/ProjectiveCount.card_trivialised_of_isHigmanProjective"),
                H("card_trivialised_of_isHigmanProjective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let V be finite, l-torsion, U-fixed, with Higman's property, z − n injective on V, and let U fix zr/rⁿ whenever r^l is an N-unit and all φ_i fix r. Trivialised cocycles number at most (#V)^{#ι+1}, exactly so if K is totally complex and z = n on μ_l.")))))));
}
