using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery.IterativePetz;

internal sealed class IterativePetzHaarDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ProcessReconstruction/lautenbacher2026iterativepetz");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict asymptotic deficit in the Haar mean of iterative Petz recovery.",
        H("Haar fidelity under single-axis dephasing"),
        Blocks(Describe.Lean(
            DescribeId.Create("mean-fidelity-limit-strict"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Recovery/IterativePetz/IterativePetzHaar.meanFidelity_tendsto_lt_one"),
            H("The limiting Haar mean is strictly below one"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "The axial distribution for a Haar-random pure qubit is uniform on the "
                + "interval from minus one to one. Each finite-depth fidelity is measurable "
                + "and bounded by one. Dominated convergence yields the limiting mean, "
                + "and the positive pointwise gap on a set of positive measure makes this "
                + "limit strictly smaller than one for every nontrivial multiplier."))),
            DescribeRole.Theorem))));
}
