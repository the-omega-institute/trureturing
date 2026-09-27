using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class DegeneracyGraphDeterminantDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Algebra/DegeneracyGraphDeterminant";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/kempramgoolam2026degeneracy");
    private static DescribeRole Role(string name) => name is "survives_step_iff" or "survives_reachesOccupied" or "survives_descendant" or "prune_survives_iff" or "column_last_occupied" or "fiberRank_order" or "det_NewtonE" or "det_NewtonE_ne_zero" ? DescribeRole.Theorem : DescribeRole.Definition;

    private static DocumentBlock.Describe Declaration(int number, string name) =>
        Describe.Lean(
            DescribeId.Create($"declaration-{number:00}"),
            DeclarationHandle.Create($"{Module}.{name}"),
            H(name),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "This public declaration is part of the source-faithful arbitrary-depth graph model. "
                + "Its displayed type is projected directly from the Lean declaration; no global grid, "
                + "uniform fiber, or depth restriction is added."))),
            Role(name));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The arbitrary-depth source tree, threshold columns, leaf-path evaluation, and determinant input are formalized with parent-dependent fibers and sibling-only labels.",
        H("Degeneracy Graph Determinant: Source Model"),
        Blocks(
            Paragraph(Text(
                "This owner records the complete public inventory of the source model. SourceTree carries "
                + "all levels and coherent ancestor maps; Survives and sourceThreshold implement the recursive "
                + "threshold rule; Columns and RawM are the literal source column and leaf-path evaluation "
                + "objects. Labels are required to be injective only within a sibling block, so unrelated "
                + "parents may reuse labels. The downstream owners consume this exact inventory in import order.")),
            Paragraph(Text(
                "The formal target is Kemp–Ramgoolam, Gauge-string duality, monomial bases and graph determinants, "
                + "arXiv:2603.05259v2, Sections 2, 3, 6, and 7. The source calls the arbitrary-depth monomial "
                + "basis and determinant statements conjectures; this delivery resolves the exact clauses only "
                + "through the stated Lean declarations. Neidinger 2019 and Sauer 2004 are recorded in the "
                + "Library note as conditional global-grid comparisons, not as proofs of this parent-dependent case.")),
            Declaration(1, "SourceTree"),
            Declaration(2, "sourcePositiveComposition"),
            Declaration(3, "Survives"),
            Declaration(4, "survivalSet"),
            Declaration(5, "survivingChildren"),
            Declaration(6, "survives_step_iff"),
            Declaration(7, "Exponents"),
            Declaration(8, "sourceThreshold"),
            Declaration(9, "sourceS"),
            Declaration(10, "Columns"),
            Declaration(11, "RawM"),
            Declaration(12, "Bottom"),
            Declaration(13, "Penultimate"),
            Declaration(14, "bottomFiber"),
            Declaration(15, "occupiedPenultimate"),
            Declaration(16, "retainedVertex"),
            Declaration(17, "reachesOccupied"),
            Declaration(18, "survives_reachesOccupied"),
            Declaration(19, "survives_descendant"),
            Declaration(20, "appendThreshold"),
            Declaration(21, "prune"),
            Declaration(22, "prune_survives_iff"),
            Declaration(23, "liftExponents"),
            Declaration(24, "restrictExponents"),
            Declaration(25, "liftColumn"),
            Declaration(26, "restrictColumn"),
            Declaration(27, "lastExponentSliceEquiv"),
            Declaration(28, "column_last_occupied"),
            Declaration(29, "depthOneExponents"),
            Declaration(30, "depthOneColumnsEquiv"),
            Declaration(31, "depthOneBottomOrder"),
            Declaration(32, "fiberOrder"),
            Declaration(33, "bottomParent"),
            Declaration(34, "bottomInFiber"),
            Declaration(35, "fiberRank"),
            Declaration(36, "fiberNewton"),
            Declaration(37, "NewtonE"),
            Declaration(38, "fiberValues"),
            Declaration(39, "fiberEvaluation"),
            Declaration(40, "fiberCoefficient"),
            Declaration(41, "fiberRank_order"),
            Declaration(42, "det_NewtonE"),
            Declaration(43, "det_NewtonE_ne_zero"))));
}
