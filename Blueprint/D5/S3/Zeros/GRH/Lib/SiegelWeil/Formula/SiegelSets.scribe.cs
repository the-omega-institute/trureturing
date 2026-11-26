using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.SiegelWeil.Formula;

internal sealed class SiegelSetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Siegel Sets", H("Siegel Sets"),
        Blocks(
            Paragraph(Text("Invariant functional small against the positive Eisenstein series vanishes, by one Hecke operator. Normal form, Siegel sets and uniform convergence of the Siegel Eisenstein series.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/SiegelWeil/Formula/SiegelSets.exists_summable_zeroTerm_bound"),
                H("exists_summable_zeroTerm_bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If rk T > 2p, there is a summable function c on the Lagrangians L of the split space S bounding, uniformly in x, the operator norm of the zero term ev_L composed with the operator normalisedTorus T P x.")))))));
}
