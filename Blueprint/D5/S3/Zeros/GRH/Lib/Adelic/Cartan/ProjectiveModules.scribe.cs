using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Cartan;

internal sealed class ProjectiveModulesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Projective Modules", H("Projective Modules"),
        Blocks(
            Paragraph(Text("Multiplicative function trivial on projective modules is trivial; Higman criterion, dévissage.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Cartan/ProjectiveModules.eq_one_of_isHigmanProjective"),
                H("eq_one_of_isHigmanProjective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let l be prime, U open normal in the compact group G, z central modulo U, and φ, with values in ℚ≥0, multiplicative in short exact sequences of finite l-torsion modules fixed by U on which z − 1 is injective. If φ = 1 on those with Higman's property, then φ = 1 on all.")))))));
}
