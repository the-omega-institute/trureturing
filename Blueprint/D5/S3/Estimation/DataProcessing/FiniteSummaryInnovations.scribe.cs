using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class FiniteSummaryInnovationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separate fresh finite scheduling and result tables realize the aggregate summary flows.",
        H("A chronological probability interpreter for summary policies"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-summary-policy-realization"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/FiniteSummaryInnovations.archive_summary_policy_realization"),
                H("Independent local pasting and one complete realization"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The actual finite archive source supplies compatible pre-result and "
                        + "post-result incidence, branch selection masses and lawful conditional "
                        + "rows. Its derived flow retains the actual source node masses and "
                        + "sums every actual branch/result mass. The source admissibility "
                        + "predicate accepts a family of scheduler "
                        + "rows and conditional result rows. The independent local pasting "
                        + "premise admits every family whose nonterminal scheduler rows "
                        + "are nonnegative and normalized and whose result rows belong "
                        + "to the corresponding common K. Under that premise, the constructed aggregate policy "
                        + "is admissible and the same actual measure satisfies every "
                        + "node, selection, result, full-prefix kernel, terminal-output "
                        + "and price-preserving additive-label conclusion below."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-summary-realized-flows"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/FiniteSummaryInnovations.realized_flows"),
                H("One actual carrier realizes all three flows"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each stage below N, a scheduling table has one named action "
                        + "cell at every summary. A separate result table has one dependent "
                        + "result cell at every pair of summary and legal action. Their "
                        + "densities are products of the normalized summary scheduler rows "
                        + "and lawful summary result rows. The generic product-row marginal "
                        + "identity supplies the marginal of each consulted cell.")),
                    Paragraph(Text(
                        "The observation alphabet at microstep 2k is the scheduling table "
                        + "for stage k. At microstep 2k+1 it is the separate result table "
                        + "for that stage. Alphabets after microstep 2N are singletons and "
                        + "are not genuine actions. The finite history law uses J equal "
                        + "to Unit, so no initial public information is concealed in the "
                        + "supplier's omitted hidden coordinate. The initial summary is "
                        + "the deterministic original root summary.")),
                    Paragraph(Text(
                        "The interpreter starts at that root. It consults the current "
                        + "scheduling cell at its public summary, then consults the current "
                        + "result cell at the selected pair, and applies public update T. "
                        + "It never consults future tables. Earlier complete tables remain "
                        + "in the recorded prefix, including unused cells. No equality "
                        + "between unused auxiliary cells before and after compression "
                        + "is asserted.")),
                    Paragraph(Text(
                        "Stage induction evaluates every real test function of the "
                        + "interpreted summary against M. The intermediate prefix after "
                        + "scheduling evaluates every test function of the actual summary "
                        + "and named action against F. The next prefix evaluates every "
                        + "test function of the actual summary, action and dependent result "
                        + "against G. Exact prefix integrals of the finite probability "
                        + "history law place all three identities on the same measure. "
                        + "Indicator tests give every node, selection and result mass.")),
                    Paragraph(Text(
                        "The complete pre-schedule archive is the prefix of length 2k; "
                        + "the pre-result archive is the prefix of length 2k+1. Source admissibility "
                        + "requires accessible summaries and independent local pasting "
                        + "with costs, permissions and resources retained. A terminal "
                        + "task must factor through the terminal summary; occupation "
                        + "identities do not preserve the whole original auxiliary "
                        + "archive or summary-path law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-summary-full-history-kernels"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/FiniteSummaryInnovations.full_history_kernels"),
                H("Full scheduling and result information order"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each nonterminal stage k, summary s and named legal action i, "
                        + "the conditional expectation of the selection indicator, given "
                        + "the entire prefix of length 2k, equals the node indicator times "
                        + "the summary scheduler probability. For every dependent result x, "
                        + "the conditional expectation of the observed-edge indicator, "
                        + "given the entire prefix of length 2k+1, equals the selection "
                        + "indicator times the legal summary result row. Both identities "
                        + "hold almost everywhere on the same probability carrier.")),
                    Paragraph(Text(
                        "The prefix conditional-expectation theorem is applied before "
                        + "evaluating a fresh table cell. At positive prefix mass its "
                        + "child-to-parent ratio is the fresh innovation density. At a "
                        + "null prefix the weighted identity and null_row_replace give "
                        + "the same almost-everywhere statement. Thus previous unused "
                        + "table cells are retained in the conditioning information, "
                        + "while the current result table is not disclosed before "
                        + "scheduling. Later tables remain outside both current prefixes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-summary-terminal-output-law"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/FiniteSummaryInnovations.terminal_output_law"),
                H("The complete specified terminal task"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the complete required terminal output o(s,h) take values "
                        + "in any measurable space. Suppose it equals one summary output "
                        + "on every terminal fiber. The pushforward of the realized "
                        + "probability measure under that summary output is exactly the "
                        + "finite sum of the original terminal node masses at their "
                        + "original output values. Equality is proved on every measurable "
                        + "set, and includes horizon zero.")),
                    Paragraph(Text(
                        "Preserving one loss can use that loss as output. Preserving "
                        + "a complete named assignment requires the terminal summary "
                        + "to recover that assignment. A live-label mask is sufficient "
                        + "only after action legality, public successors and the entire "
                        + "specified task output are shown to be constant on its fibers. "
                        + "This theorem makes no claim about the whole original "
                        + "auxiliary archive or summary-path law."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-summary-expected-additive-price"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/FiniteSummaryInnovations.archive_expected_additive_price"),
                H("Prices, permissions and resources"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A real transition label at (k,s,i,x) preserves expected additive "
                        + "cost when every original edge in that fiber has precisely "
                        + "that price. The expectation of the sum of realized labels "
                        + "then equals the original sum over actual compatible successors of "
                        + "their actual masses times their source price. The source price "
                        + "must equal that label on every pre-record, result and post-record "
                        + "incidence. Negative labels are also permitted. "
                        + "Preserving the entire cost-path law requires its record in "
                        + "the summary and terminal task. Convexity alone does not "
                        + "preserve nonlinear charges on row selection; such charges "
                        + "must satisfy an explicit price-preservation contract.")),
                    Paragraph(Text(
                        "These are sufficient conditions. State information must come "
                        + "from the actual accessible archive. Hidden remaining budgets, "
                        + "unread source values and future innovations cannot become "
                        + "public merely by being named as state. Finite posterior state "
                        + "requires a separately verified public update. Permissions and "
                        + "resources affecting admissibility must be retained. Independent "
                        + "local pasting excludes an unrecorded common external model "
                        + "index or cross-branch compatibility constraint; adding a path "
                        + "budget does not remove such a coupling. Polyhedral row sets "
                        + "are needed only for a requested finite linear-flow description, "
                        + "not for the convex aggregation and realization theorem.")),
                    Paragraph(Text(
                        "A finite pre-result record may select different lawful rows. Its "
                        + "actual selection masses determine the convex average before the "
                        + "fresh result is sampled. A post-result record instead partitions "
                        + "the mass of each already acquired actual result over compatible "
                        + "successor archives. Neither kind of record enlarges the named "
                        + "action or its result alphabet. The complete archive realization "
                        + "uses their derived M, F and G on the same fresh measure, and "
                        + "includes full chronological kernels, terminal task factorization "
                        + "and explicitly price-preserving source incidence labels."))),
                DescribeRole.Theorem))));
}
