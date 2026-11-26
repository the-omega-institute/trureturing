using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Rows;

internal sealed class LiftVolumeHeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lift Volume Height", H("Lift Volume Height"),
        Blocks(
            Paragraph(Text("Height bound for untwisted over twisted volume of one lift on good forms.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Rows/LiftVolumeHeight.heightLe_liftVolume_ratio"),
                H("heightLe_liftVolume_ratio"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For m-fold twists θ(ι) satisfying Data.IsFitFamily and 1 ≤ j ≤ m, the volume ratios λ_j(1)/λ_j(θ(ι)^j) (Data.liftVolume) have height (HeightLe) at most d·k·(B₀·log b − 𝖴), with d the dimension of Data.rows and 𝖴 = Data.dirCost (size of a jet less its forced divisibility), B₀ = fa(log b)³/(mk) = Data.B₀.")))))));
}
