using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class PartialAssignmentOccupancyFlowDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial assignment occupancy flows and terminal laws.",
        H("Partial assignment occupancy flows and terminal laws"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("partial-assignment-last-coordinate-partition"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.incomingAppend_bijective"),
                H("Every incoming last coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A state is a dependent function assigning either no value or one actual "
                    + "letter to each coordinate in a fixed finite nonempty named set. "
                    + "Capacities lie between reciprocal alphabet cardinality and one. "
                    + "The alphabets are finite and "
                    + "nonempty and can have different sizes. Erasure discards the read order "
                    + "and preserves all coordinate identities and obtained values. Its rank "
                    + "is the number of assigned coordinates, equal to the history length. "
                    + "Each history arriving at a state has a unique last coordinate. The "
                    + "bijection partitions its entire history fiber over every assigned "
                    + "coordinate and the history fiber of the state with that coordinate "
                    + "deleted. Distinct orders can therefore merge at one state."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-assignment-incoming-conservation"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.aggregate_incoming"),
                H("Literal incoming conservation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Summing ordered node, selection and result masses on the erasure fibers "
                    + "gives the occupancy variables. The last-coordinate partition turns the "
                    + "sum of child node masses into the sum of result flows from all deleted "
                    + "parents. Summing the remaining ordered-flow constraints gives root mass "
                    + "one, outgoing conservation, result normalization, nonnegativity and "
                    + "the original coordinate cap. Occupancy feasibility assumes these "
                    + "literal equations and does not assume an ordered lifting witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-assignment-all-mass-inverse"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.lift_all_masses"),
                H("Constructive inverse on every mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a positive node the global scheduler row is selection mass divided "
                    + "by node mass. At a positive selection the result row is result mass "
                    + "divided by selection mass. Null nodes use a uniform row on the actual "
                    + "unread coordinates, and null selections use the uniform row on their "
                    + "own alphabet. The lower capacity bound makes these fallback rows "
                    + "lawful. Weighted row identities hold also at zero denominators. "
                    + "Ordered masses are built recursively from these rows. Induction on "
                    + "rank, using all deleted parents and incoming conservation, recovers "
                    + "every node mass. The weighted identities then recover every selection "
                    + "and result mass, including null branches."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-assignment-aggregate-lift"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.aggregate_lift"),
                H("Equality of occupancy flows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Aggregating the constructed ordered flow gives the original occupancy "
                    + "flow in all three variable families. The inverse preserves the entire "
                    + "finite flow, rather than only a terminal statistic."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-assignment-archive-realization"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.realize_occupancy_state_strategy"),
                H("Fresh lawful archive realization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constructed ordered flow is supplied to the ordered archive "
                    + "realization theorem. Its separate fresh scheduling and result table "
                    + "innovations retain every completed block, reveal current scheduling "
                    + "before the result, and check the conditional cap on that complete "
                    + "accessible archive. On this same actual carrier, literal erased-state "
                    + "node, selection and result events have exactly the prescribed masses. "
                    + "The complete pre-schedule archive F gives the scheduler kernel "
                    + "one_Node times sigma; the archive G, which also discloses the current "
                    + "scheduler innovation, gives the result kernel one_Selection times q. "
                    + "Both identities hold almost everywhere. At a complete assignment the node "
                    + "mass is the entire named terminal joint law. This construction uses "
                    + "cap-only rectangular row pasting: arbitrary legal rows at different "
                    + "histories must be independently selectable."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-assignment-actual-event-masses"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_event_masses"),
                H("Actual disjoint state events"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The literal node event fixes the erased assignment of the actual history. "
                    + "Selection also fixes the named coordinate; result also fixes its actual "
                    + "letter in the dependent alphabet. Each event is the disjoint union of "
                    + "its ordered-history fibers on the canonical fresh archive. Finite disjoint "
                    + "probability sums and the all-mass inverse give respectively M(a), F(a,i) "
                    + "and F(a,i,x), including zero-mass states and edges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-assignment-full-f-scheduler"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_scheduler_kernel"),
                H("Scheduling under the complete F archive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Before schedule disclosure, F retains all past scheduler and result "
                    + "innovation blocks. Independence of the next block and its scheduler "
                    + "marginal give the ordered scheduler conditional expectation. The weighted "
                    + "ordered row equals node mass times the global erased-state row. A positive "
                    + "mass permits cancellation; a zero mass makes its actual event null and "
                    + "permits almost-everywhere replacement. Summing disjoint history fibers "
                    + "gives E[one_Selection | F] = one_Node times sigma. This is a property of "
                    + "the new reverse realization, not of every original archive strategy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-assignment-full-g-result"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.state_result_kernel"),
                H("Results under the complete G archive"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "G retains all previous innovation blocks and the full currently disclosed "
                    + "scheduler table, while the current result innovation stays fresh. The "
                    + "existing ordered full-G conditional result theorem is reused directly. "
                    + "Selection mass times its ordered row equals selection mass times the "
                    + "global q row. Cancellation on positive selections and null-event "
                    + "replacement on zero selections allow finite fiber aggregation, giving "
                    + "E[one_Result | G] = one_Selection times q almost everywhere. Unused "
                    + "auxiliary table cells need not agree pointwise across erased histories."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("partial-assignment-terminal-law-range"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/PartialAssignmentOccupancyFlow.occupancy_terminal_law_range"),
                H("Exact terminal law set"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The range of terminal occupancy laws equals archiveTerminalLaws, the "
                    + "existing set of terminal laws of legal actual archived strategies. "
                    + "The forward statement also applies to an original strategy on an "
                    + "arbitrary probability space with arbitrary additional retained "
                    + "records. No finite-history restriction is imposed on that original "
                    + "archive. The compression preserves terminal joint laws, including "
                    + "correlations, but does not preserve original read-order distributions "
                    + "or auxiliary-record joint laws. Source compatibility, permissions or "
                    + "costs that depend on order require additional state information; the "
                    + "cap-only assumption does not remove those restrictions. The finite "
                    + "state space can still grow exponentially, so existence of this exact "
                    + "representation supplies no low-cost extraction or solution claim."))),
                DescribeRole.Theorem))));
}
