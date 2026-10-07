using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Walk;

internal sealed class StoppedShortfallDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Walk/StoppedShortfall.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian matrix walk, filtration and stopped increments.",
        H("Stopped Shortfall"),
        Blocks(
            Paragraph(Text("Gaussian matrix walk, filtration and stopped increments. The results below relate stopped shortfall to the stochastic ellipsoid construction.")),
            Node("claim-1", "sum_norm_liftStep_le", "sum norm lift Step le",
                "∑_{j<K} ‖ℓ_j‖ ≤ card(C_K)·η, the intermediate step of LiftBound.norm_liftSum_le_card.", DescribeRole.Theorem),
            Node("claim-2", "sum_sq_le_sq_sum", "sum sq le sq sum",
                "A sum of squares of non-negatives is at most the square of the sum.", DescribeRole.Theorem),
            Node("claim-3", "sum_liftStep_sq_le", "sum lift Step sq le",
                "∑_{j<K} ‖ℓ_j‖² ≤ (c₃η)² on a path whose count stays below c₃.", DescribeRole.Theorem),
            Node("claim-4", "norm_gaussStep_sq_le_trunc", "norm gauss Step sq le trunc",
                "‖π_jξ_j‖² ≤ min(‖ξ_j‖², η²) whenever the raw step is capped by η.", DescribeRole.Theorem),
            Node("claim-5", "logDet_stopped_ge_final", "log Det stopped ge final",
                "The pathwise lower bound ShortfallBound.shortfall_le consumes. M is LogDetMartingale.mgPart … K, whose second moment is variance_M_le; D is a non-negative multiple of the truncated chi-square sum, a constant, and MidTerm.midCap, all three measurable with deterministic ranges.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
