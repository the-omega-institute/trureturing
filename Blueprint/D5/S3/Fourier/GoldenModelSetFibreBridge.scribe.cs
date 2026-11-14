using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class GoldenModelSetFibreBridgeDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Fourier/GoldenModelSetFibreBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The floor-selected golden model-set lift fills every internal fibre and recovers the golden mechanical word on natural fibres.",
        H("Golden Model-Set Fibres and the Mechanical Word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-model-set-fibre-lift-window-membership"),
                DeclarationHandle.Create(Gid + "golden_window_fiber_lift_mem"),
                H("Every internal fibre has a window lift"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each integer internal coordinate b, the floor-selected integral coordinate "
                    + "places the conjugate embedding in the closed golden window."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-model-set-fibre-witness"),
                DeclarationHandle.Create(Gid + "golden_modelSet_fiber_witness"),
                H("The lift is a model-set witness"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The same floor-selected lift supplies an explicit witness that its physical "
                    + "embedding belongs to the existing golden model set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-model-set-fibre-natural-coordinate"),
                DeclarationHandle.Create(Gid + "golden_window_fiber_lift_a_nat"),
                H("Natural-fibre coordinates are Beatty floors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On a nonnegative fibre n, the selected integral coordinate is the Beatty "
                    + "floor at the golden mechanical slope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-model-set-fibre-mechanical-step"),
                DeclarationHandle.Create(Gid + "golden_window_fiber_step"),
                H("Successive fibre coordinates are mechanical letters"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The difference between consecutive natural-fibre coordinates equals the "
                    + "corresponding golden mechanical letter."))),
                DescribeRole.Theorem))));
}
