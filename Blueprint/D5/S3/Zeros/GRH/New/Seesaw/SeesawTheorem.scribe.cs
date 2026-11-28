using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class SeesawTheoremDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Seesaw Theorem", H("Seesaw Theorem"),
        Blocks(
            Paragraph(Text("Seesaw identity for the chain of lifts, by downward induction with finite cuts.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/SeesawTheorem.seesaw"),
                H("seesaw"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The seesaw identity: there is a non-zero complex number c such that for every twist ϑ some good datum Ψ (Data.IsGoodDatum) has ι(𝒫(cφ)) = B^Ψ φ for all ramified columns φ; 𝒫 is the Poincaré series, ι = Data.ι the chain of m theta lifts through the spaces Y_j, and B^Ψ = Data.Bμ the chain through the definite spaces X_j with finite datum Ψ, restricted to Y_m.")))))));
}
