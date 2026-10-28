using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class SubstochasticEscapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SubstochasticEscape", H("Strict substochastic escape, nonsingularity and the Neumann series"), Blocks(
            Paragraph(Text("A real nonnegative matrix has row sums at most one. A common positive power has every row sum bounded by a real constant strictly below one. Monotonicity of row sums and the block estimate make every matrix-power entry tend to zero. A vector fixed by the matrix is fixed by every power, so the kernel of I minus the matrix is zero. The geometric finite-sum identity also gives the entrywise Neumann series: the powers sum to the inverse of I minus the matrix. No irreducibility or integer invertibility is used.")),
            Paragraph(Text("The statements and proof bodies are the substochastic escape and Neumann-series results in EAB.Paper.Chain, from YuZh98/aldous-broder-lean at bd20382923d987fc54a9773e04a4bc22b851872c. The source EAB/Paper/ConfinedChain.lean has SHA256 d235b9788731933c6f9b315b164ed71859748ca44658eef3cf033acfefbb8fba. Copyright 2026 Hugh Zheng; the full Apache 2.0 licence and original notice are in docs/reports/licenses/aldous-broder-substochastic.md.")),
            Paragraph(Text("The supplier pins Lean 4.30.0 and Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f; the repository pins Lean 4.33.0 and Mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The owning namespace and imports are adapted. MatrixFoundation is omitted because this slice consumes no declarations from it; Matrix.pow_apply_nonneg is supplied directly by Mathlib.Data.Matrix.Mul. SpecificLimits.Basic, Matrix.ToLinearEquiv and Topology.Instances.Matrix supply the other live dependencies. No statement type or proof body is adapted.")),
            Paragraph(Text("The scaling/positive determinant, irreducible and confined-chain developments are omitted. The decay and nonsingularity results determine the actual transient block, and the Neumann series gives summability of its first-entry weights. Retire this port when this repository's pinned Mathlib contains equivalent declarations and replace the live applications by direct reuse.")),
            Paragraph(Text("The rowSum function records the total mass remaining after a fixed number of transitions. Nonnegative powers allow each entry to be bounded by its row sum. Splitting a power into two blocks gives a row-sum bound by the product of the earlier row sum and a uniform bound on the later block.")),
            Paragraph(Text("Substochasticity makes each row sum nonincreasing in time. If every row loses a uniform positive amount of mass after N transitions, with N positive, repeated N-step blocks give a geometric upper bound. Division by N extends this bound to arbitrary times and forces each power entry to converge to zero.")),
            Paragraph(Text("If I minus the matrix were singular, a nonzero vector would be fixed by the matrix and hence by every matrix power. Entrywise convergence and finiteness of the carrier force the same vector to be zero, a contradiction. This nonsingularity result applies to the internal substochastic matrix in the finite fair-bit exit denominator argument.")),
            Node("statement-0", "pow_nonneg", "Every natural power of a finite real substochastic matrix has nonnegative entries."),
            Node("statement-1", "rowSum_zero", "For every finite real square matrix and row, the row sum of its zeroth power is one."),
            Node("statement-2", "rowSum_one", "For every finite real square matrix, the row sum of its first power is the sum of the original entries in that row."),
            Node("statement-3", "rowSum_add", "For every finite real square matrix and natural exponents a and b, the row sum at a plus b is the sum over intermediate states of the a-th power entry times the b-th power row sum."),
            Node("statement-4", "rowSum_nonneg", "Every row sum of every natural power of a finite real substochastic matrix is nonnegative."),
            Node("statement-5", "entry_le_rowSum", "Each entry of a natural power of a finite real substochastic matrix is bounded above by the sum of its row."),
            Node("statement-6", "rowSum_add_le", "If every row sum of the b-th power of a finite real substochastic matrix is at most a real number c, then each row sum at exponent a plus b is at most c times the corresponding row sum at exponent a."),
            Node("statement-7", "rowSum_succ_le", "For a finite real substochastic matrix, each row sum at exponent t plus one is at most its row sum at exponent t."),
            Node("statement-8", "rowSum_antitone", "For a finite real substochastic matrix and fixed row, the sequence of power row sums is antitone."),
            Node("statement-9", "rowSum_mul_le", "If every row sum of the N-th power of a finite real substochastic matrix is at most c, then every row sum of its m times N-th power is at most c to the power m, for every natural m."),
            Node("statement-10", "tendsto_pow_entry", "For a finite real substochastic matrix, assume a positive natural N and a real c strictly below one bound every row sum of the N-th power. Every entry of the natural matrix powers then tends to zero."),
            Node("statement-11", "det_one_sub_ne_zero", "For a finite real substochastic matrix, assume a positive natural N and a real c strictly below one bound every row sum of the N-th power. The determinant of the identity minus the matrix is then nonzero."),
            Node("statement-12", "hasSum_pow_entry", "For a finite real substochastic matrix, assume a positive natural N and a real c strictly below one bound every row sum of the N-th power. The series of each matrix-power entry, starting at exponent zero, sums to the corresponding entry of the inverse of the identity minus the matrix."))));
    private static DocumentBlock.Describe Node(string id, string name, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Observer/zheng2026substochastic")),
            Blocks(Paragraph(Text(statement))),
            DescribeRole.Theorem);
}
