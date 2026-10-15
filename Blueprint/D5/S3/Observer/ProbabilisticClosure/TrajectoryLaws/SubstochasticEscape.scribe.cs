using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;
internal sealed class SubstochasticEscapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/SubstochasticEscape.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SubstochasticEscape", H("Strict substochastic escape and nonsingularity"), Blocks(
            Paragraph(Text("A real nonnegative matrix has row sums at most one. A common positive power has every row sum bounded by a real constant strictly below one. Monotonicity of row sums and the block estimate make every matrix-power entry tend to zero. A vector fixed by the matrix is fixed by every power, so the kernel of I minus the matrix is zero. No irreducibility or integer invertibility is used.")),
            Paragraph(Text("The rowSum function records the total mass remaining after a fixed number of transitions. Nonnegative powers allow each entry to be bounded by its row sum. Splitting a power into two blocks gives a row-sum bound by the product of the earlier row sum and a uniform bound on the later block.")),
            Paragraph(Text("Substochasticity makes each row sum nonincreasing in time. If every row loses a uniform positive amount of mass after N transitions, with N positive, repeated N-step blocks give a geometric upper bound. Division by N extends this bound to arbitrary times and forces each power entry to converge to zero.")),
            Paragraph(Text("If I minus the matrix were singular, a nonzero vector would be fixed by the matrix and hence by every matrix power. Entrywise convergence and finiteness of the carrier force the same vector to be zero, a contradiction. This nonsingularity result applies to the internal substochastic matrix in the finite fair-bit exit denominator argument.")),
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
