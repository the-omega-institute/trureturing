using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class SubstochasticEscapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SubstochasticEscape", H("Strict substochastic escape and nonsingularity"), Blocks(
            Paragraph(Text("A real nonnegative matrix has row sums at most one. A common positive power has every row sum bounded by a real constant strictly below one. Monotonicity of row sums and the block estimate make every matrix-power entry tend to zero. A vector fixed by the matrix is fixed by every power, so the kernel of I minus the matrix is zero. No irreducibility or integer invertibility is used.")),
            Paragraph(Text("The statements and proof bodies are the live dependency slice of EAB.Paper.Chain.IsSubstochastic.det_one_sub_ne_zero, from YuZh98/aldous-broder-lean at bd20382923d987fc54a9773e04a4bc22b851872c. The source EAB/Paper/ConfinedChain.lean has SHA256 d235b9788731933c6f9b315b164ed71859748ca44658eef3cf033acfefbb8fba. Copyright 2026 Hugh Zheng; the full Apache 2.0 licence and original notice are in docs/reports/licenses/aldous-broder-substochastic.md.")),
            Paragraph(Text("The supplier pins Lean 4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f; the repository pins Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The owning namespace and imports are adapted. MatrixFoundation is omitted because this slice consumes no declarations from it; Matrix.pow_apply_nonneg is supplied directly by Mathlib.Data.Matrix.Mul. SpecificLimits.Basic, Matrix.ToLinearEquiv and Topology.Instances.Matrix supply the other live dependencies. No statement type or proof body is adapted.")),
            Paragraph(Text("The unused rowSum_le_one leaf and the entire Neumann series, scaling/positive determinant, irreducible and confined-chain development are omitted. Every retained helper is consumed by the next row-sum or convergence proof, and det_one_sub_ne_zero is consumed by FiniteFairBitDenominator.det_ne_zero. Retire this port when this repository's pinned Mathlib contains equivalent declarations and replace the live applications by direct reuse.")),
            Node("statement-0", "pow_nonneg"),
            Node("statement-1", "rowSum_zero"),
            Node("statement-2", "rowSum_one"),
            Node("statement-3", "rowSum_add"),
            Node("statement-4", "rowSum_nonneg"),
            Node("statement-5", "entry_le_rowSum"),
            Node("statement-6", "rowSum_add_le"),
            Node("statement-7", "rowSum_succ_le"),
            Node("statement-8", "rowSum_antitone"),
            Node("statement-9", "rowSum_mul_le"),
            Node("statement-10", "tendsto_pow_entry"),
            Node("statement-11", "det_one_sub_ne_zero"))));
    private static DocumentBlock.Describe Node(string id, string name) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The compiled statement includes its complete displayed premises."))),
            DescribeRole.Theorem);
}
