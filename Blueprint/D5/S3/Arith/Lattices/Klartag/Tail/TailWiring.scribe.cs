using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Tail;

internal sealed class TailWiringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Tail/TailWiring.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lattice tail bounds along the matrix walk.",
        H("Tail Wiring"),
        Blocks(
            Paragraph(Text("Lattice tail bounds along the matrix walk. The results below relate tail wiring to the stochastic ellipsoid construction.")),
            Node("claim-1", "Wg", "Wg",
                "Abbreviation for the chain the drift side runs: the reach-2 window, the chain's own q and A₀, and the adopted Gaussian step.", DescribeRole.Definition),
            Node("claim-3", "intWeight_mono_steps", "int Weight mono steps",
                "intWeight is monotone in the step count.", DescribeRole.Theorem),
            Node("claim-4", "intWeight_le_prof_win", "int Weight le prof win",
                "The integrated bound on windowOfR2, pointwise and real. intWeight_leRW2 at the window, then intWeight_mono_steps down to any K ≤ N.", DescribeRole.Theorem),
            Node("claim-5", "htail_win", "htail win",
                "The terminal bound on windowOfR2, in the exact htail shape — 2·weight + 0 with weight y = 2·profileAt … (horizon (m+1)) ‖toE (m+1) y‖, at every K < N.", DescribeRole.Theorem),
            Node("claim-9", "sum_lt_of_sum_ofReal", "sum lt of sum of Real",
                "A sum of ENNReal.ofReals below ENNReal.ofReal Θ is a real strict inequality.", DescribeRole.Theorem),
            Node("claim-10", "sums_at_windowOfR2", "sums at window Of R2",
                "The two sums, from one light-contact hypothesis at the combined profileAt family. The first is FinalDischarge2.hS_of_intWeight_wired's hlight; the second is TerminalCount.countGood_of_terminal_weight's hθ, at the weight htail_win supplies.", DescribeRole.Theorem),
            Node("claim-11", "hS_light_win", "h S light win",
                "hS's hypothesis, in FinalDischarge2.hS_of_intWeight_wired's exact shape (≤).", DescribeRole.Theorem),
            Node("claim-12", "hcnt_win", "hcnt win",
                "hcnt, finished — TerminalCount.countGood_of_terminal_weight at htail_win and the second sum. Holds at every K < N, so the count index is the caller's choice.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
