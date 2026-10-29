using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeFourCurrentTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Characters/LatticeFourCurrentTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite four-current traces on the original complete energy grades.",
        H("Finite Four-Current Trace"),
        Blocks(
            Definition("lattice-four-current-cycle", "actualFourCurrentCycleTrace", "Original finite four-current cycle trace",
                "The trace is the finite complex LinearMap.trace of the right-to-left composition of the four literal actualCurrentBlock maps on the initial original grade."),
            Definition("lattice-four-current-coefficient", "boundedFourCurrentCoefficient", "Bounded ten-matching coefficient",
                "The coefficient sums over the positive charge cutoff, the ten labeled matchings, bounded positive frequencies, two arc choices, bounded windings, and bounded residual grade, with guarded full-grade equalities and signed Gram and zero-mode factors."),
            Paragraph(Text("The source defines the complete finite objects and compiles the equal-grade zero-mode basis bridge internally. The signed-mode CCR recurrence and the all-grade transport to the displayed coefficient remain open proof obligations; no analytic convergence or full string/AdS claim is made.")))));

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
