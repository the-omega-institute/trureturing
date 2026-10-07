using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices.Klartag.Drift;

internal sealed class DriftAccumulatedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Lattices/Klartag/Drift/DriftAccumulated.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/klartag2025packing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Second order log determinant bounds and accumulated drift.",
        H("Drift Accumulated"),
        Blocks(
            Paragraph(Text("Second order log determinant bounds and accumulated drift. The results below relate drift accumulated to the stochastic ellipsoid construction.")),
            Node("claim-1", "sum_good_le_of_prefix", "sum good le of prefix",
                "DriftStopped5.sum_good_le with the freeze count removed. The indicator restricts the sum to k < τ ω − 1, i.e. to Finset.range (min m (τ ω − 1)), and that index is < τ ω; so a single prefix-sum bound at one index replaces \"dim E freezes, each costing ε\".", DescribeRole.Theorem),
            Node("claim-2", "sum_stoppedErr_le_acc", "sum stopped Err le acc",
                "DriftStopped5.sum_stoppedErr_le with the accumulated total. Only the good-range summand changes; the middle case is still one increment read at τ − 1.", DescribeRole.Theorem),
            Node("claim-3", "integral_sum_stoppedErr_le_acc", "integral sum stopped Err le acc",
                "DriftStopped6.integral_sum_stoppedErr_le with the accumulated total.", DescribeRole.Theorem),
            Node("claim-4", "sum_integral_stoppedErr_le_acc", "sum integral stopped Err le acc",
                "DriftStopped6.sum_integral_stoppedErr_le with the accumulated total — the shape ChainDrift.drift_bound consumes.", DescribeRole.Theorem),
            Node("claim-5", "drift_bound_stopped_acc", "drift bound stopped acc",
                "DriftStopped6.drift_bound_stopped_maximal with the accumulated total. This is a *re-instantiation*: DriftStopped6.drift_bound_stopped already takes the error total E as an input, so only the argument supplied for it changes.", DescribeRole.Theorem),
            Node("claim-6", "driftRHS_acc", "drift RHS acc",
                "GoodPathBounds.driftRHS with the error total free. driftRHS n A₀ c₃ ε S is driftRHS_acc n A₀ c₃ (dim E · ε) S definitionally (driftRHS_eq).", DescribeRole.Definition),
            Node("claim-7", "drift_bound_at_acc", "drift bound at acc",
                "The accumulated prefix error bound controls determinant drift up to a good cut, with total error E in place of a separate charge for every active-set change.", DescribeRole.Theorem),
            Node("claim-10", "sum_chainErr_le_c3", "sum chain Err le c3",
                "The prefix-sum hypothesis, discharged. ChainErrBudget.sum_chainErr_le_of_lt_tau gives |C_K|·η/m; stateGood K (available because K < τ) gives |C_K| ≤ c₃.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string heading, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(heading),
            StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), role);
}
