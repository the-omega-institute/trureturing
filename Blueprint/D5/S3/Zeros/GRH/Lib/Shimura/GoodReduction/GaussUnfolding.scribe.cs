using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.GoodReduction;

internal sealed class GaussUnfoldingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gauss Unfolding", H("Gauss Unfolding"),
        Blocks(
            Paragraph(Text("Mean of the theta kernel as Gauss sum times Gaussian integral; real fourth power.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/GoodReduction/GaussUnfolding.isSelfAdjoint_quotMean_pow"),
                H("isSelfAdjoint_quotMean_pow"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If c − c̄ acts invertibly on V, the mean over V/L of x ↦ K(c̄x, cx), times the complex conjugate of det(c̄ | V), has real fourth power; K is the Poincaré series IsAppellHumbert.poincareSeries for B and the canonical multiplier of β.")))))));
}
