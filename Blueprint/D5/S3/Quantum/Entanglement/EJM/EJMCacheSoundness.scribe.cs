using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMCacheSoundnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMCacheSoundness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact local cache updates preserve the full projected assignment and bound the unchanged EJM score.",
        H("Local cache soundness for the actual EJM score"),
        Blocks(
            Paragraph(Text("The twenty inflation coordinates have four outcomes. Each global cache contains sixteen ten-coordinate triangle rows and sixteen nine-coordinate singleton rows. A row index and its entire coordinate and outcome action remain associated with the original projected partial assignment; a scalar lower alone cannot supply the update invariant.")),
            Paragraph(Text("The concrete premises exhaust all 41,294 triangle rows and 8,689 singleton rows, all unknown-coordinate updates at every outcome, the complete local bound DAGs, and the terminal contraction and tag checks. These numerical premises are proved in the same delivery and are used by the cache soundness proofs. No producer observation is a mathematical assumption.")),
            Item("triangle-step", "triangle_step_valid", "A triangle row remains associated after a fill",
                "For any valid triangle row and partial assignment, filling any currently unknown coordinate at any of the four outcomes preserves the complete row association and the exact updated partial assignment. The transition's full canonical coordinate and outcome action is composed with the current action."),
            Item("singleton-step", "singleton_step_valid", "A singleton row remains associated after a fill",
                "The corresponding statement covers every valid singleton row, every unknown coordinate and every outcome, with the complete action retained."),
            Item("global-step", "step_associated", "A global fill preserves every actual local projection",
                "For every associated cache and global partial assignment, any unknown global-coordinate fill preserves association to the updated assignment in all thirty-two placements. Injective incidence laws derive each affected local update; unaffected projections stay associated."),
            Item("initial-associated", "initial_associated", "The actual initial cache represents the empty original assignment",
                "Both actual root rows have the empty assignment. Their full identity actions establish association in all thirty-two placements, giving the exact starting invariant for every subsequent unknown fill. This reuses the existing checked same-certificate initialization proof."),
            Item("triangle-bound", "triangle_valid_lower", "Every compatible triangle completion satisfies its lower",
                "For any valid cached triangle row and any complete local event compatible with the represented partial assignment, its stored integer lower is at most the original centered triangle score with the exact pinned coefficient function F1. Complete local acceptance and score invariance discharge the numeric premises."),
            Item("singleton-bound", "singleton_valid_lower", "Every compatible singleton completion satisfies its lower",
                "The corresponding lower bound applies to the original centered singleton score with the exact pinned coefficient function F2."),
            Item("score-bound", "associated_lower_le_score", "All thirty-two local bounds control the original score",
                "For every globally associated cache, every represented partial assignment and every compatible complete event, the sum of its thirty-two stored lowers is at most the unchanged actual integer EJM inflation score. The proof applies the earned local inequalities to the actual injective placements and sums them."),
            Paragraph(Text("This result validates the local cache and lower-bound part of the certificate pipeline. It supplies neither complete global search acceptance nor a positive global score margin. Nonlocality of the ideal EJM law and a concrete source-noise region still require those further proofs; this local delivery makes no such claim.")))));

    private static DocumentBlock Item(string id, string declaration, string title, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
