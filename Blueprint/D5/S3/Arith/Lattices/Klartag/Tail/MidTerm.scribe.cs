using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class MidTermDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/MidTerm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Mid Term"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate mid term to the stochastic ellipsoid construction.")),
            Node("claim-3", "mgIncr_eq_inner", "mg Incr eq inner",
                "Below the stopping time the stopped coefficient is the chain's own.", DescribeRole.Theorem),
            Node("claim-4", "mid", "mid",
                "The single step the two cuts disagree on.", DescribeRole.Definition),
            Node("claim-5", "mid_eq", "mid eq",
                "mid is one increment or nothing.", DescribeRole.Theorem),
            Node("claim-6", "mid_sq_le", "mid sq le",
                "mid² ≤ ∑_{j<K} Δ_j² — at most one summand is non-zero.", DescribeRole.Theorem),
            Node("claim-7", "sum_Vcoef_eq", "sum Vcoef eq",
                "∑_{j < min K (τ−1)} ⟪V_j, ξ_j⟫ = mgPart … K − mid. The telescoped sum of StoppedLowerBound.logDet_stopped_ge in terms of the martingale LogDetMartingale bounds.", DescribeRole.Theorem),
            Node("claim-8", "midCap", "mid Cap",
                "midCap — √(∑_{j<K} Δ_j²), which dominates mid and, unlike it, is a function of a deterministic range, so every measurability and integrability fact about it comes straight from LogDetMartingale's per-increment exports. Charging midCap rather than mid to the drift side costs nothing: both have second moment at most varBound ≈ 1.4·10⁻⁴.", DescribeRole.Definition),
            Node("claim-11", "mid_le_midCap", "mid le mid Cap",
                "mid ≤ midCap.", DescribeRole.Theorem),
            Node("claim-12", "sum_Vcoef_ge", "sum Vcoef ge",
                "The stopped accumulation, with a measurable drift charge. mgPart … K is the deterministic martingale of LogDetMartingale; midCap is the extra drift charge.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
