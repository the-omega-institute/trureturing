using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class FiniteSummaryAggregationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite original history fibers aggregate convex legal rows and preserve incoming mass.",
        H("Aggregation of a finite history tree by a public summary"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-summary-incoming-conservation"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/FiniteSummaryAggregation.archive_incoming_conservation"),
                H("The original successor partition"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a horizon N. At stage k, S(k) is the finite summary space and "
                        + "H(k,s) is the finite fiber of original histories with summary s. "
                        + "An original node is the pair (s,h). The finite named legal actions "
                        + "A(k,s) and their dependent finite result alphabets X(k,s,i) are shared "
                        + "throughout each fiber. Nonterminal summaries have a legal action; "
                        + "no action is required at the terminal layer. The fixed original root "
                        + "determines its initial summary.")),
                    Paragraph(Text(
                        "The actual successor incidence has parent (s,h), actual named action i, "
                        + "a finite pre-result scheduling record r, actual dependent result x, and "
                        + "a compatible post-result record t. Pre-record types depend on the "
                        + "parent and action; post-record types depend on the full parent, action, "
                        + "pre-record and result. The incidence equivalence enumerates each actual "
                        + "next archive exactly once. It does not pair every coarse edge with the "
                        + "whole next-summary fiber. Empty compatible fibers are permitted.")),
                    Paragraph(Text(
                        "The source supplies node mass m, actual pre-result selection branch "
                        + "mass f(s,h,i,r), and its lawful G-conditional row q(s,h,i,r). Branch "
                        + "masses are nonnegative and sum over actions and records to m. Every "
                        + "row belongs to the same arbitrary nonempty convex K(s,i). For each "
                        + "actual branch/result, the masses of its compatible actual children "
                        + "sum to f times q. This local source partition is the finite "
                        + "conditional probability balance, including zero-mass branches.")),
                    Paragraph(Text(
                        "M sums actual node masses over a summary fiber. F sums actual selection "
                        + "branch masses over original archives and pre-records. G sums f times "
                        + "q over those same archives and pre-records. The proof sums the actual "
                        + "incidence equivalence, then the local post-result partition. Public "
                        + "update T(s,i,x) identifies the successor summary. This derives every "
                        + "incoming summary balance; aggregate incoming conservation is not "
                        + "an assumption of ArchiveFlow."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-summary-recursive-mass"),
                DeclarationHandle.Create(
                    "D5/S3/Estimation/DataProcessing/FiniteSummaryAggregation.recursive_mass"),
                H("Lawful normalized rows and the recursive summary law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At a positive node mass, the scheduler is F divided by M. At a "
                        + "null node it is the normalized uniform row on its nonempty legal "
                        + "action set. At a positive selection mass, the result row is the "
                        + "finite center of mass of the original q rows, with selection "
                        + "weights f. Convex.centerMass_mem proves membership in arbitrary "
                        + "K; closedness and polyhedrality are not assumed. At a null "
                        + "selection, choose an actual member of K. Uniform results are "
                        + "not presumed lawful.")),
                    Paragraph(Text(
                        "Nonnegative conservation makes every selection vanish at a null "
                        + "node and every original selection in a null selection fiber "
                        + "vanish. Consequently M times the scheduler equals F and F times "
                        + "the result row equals G on every branch. The summary law starts "
                        + "at the deterministic root summary and recursively transports "
                        + "these normalized rows through T. Induction, using the original "
                        + "incoming partition, proves equality with M at every stage at "
                        + "most N, including N equal to zero.")),
                    Paragraph(Text(
                        "This recurrence is an algebraic summary law. A probability "
                        + "interpreter must additionally realize it with scheduling before "
                        + "results, and must verify conditional rows on the complete "
                        + "accessible archives. Local row membership is physically usable "
                        + "only when the original admissibility contract allows independent "
                        + "nodewise row and continuation pasting. Hidden budgets, permissions "
                        + "and common external model indices cannot be erased by these "
                        + "finite-sum identities.")),
                    Paragraph(Text(
                        "ArchiveFlow.toFlow first averages the lawful rows at the actual "
                        + "pre-result branches, using their selection masses. At a null "
                        + "selection it uses an actual member of K. pre_weighted proves "
                        + "that this finite averaging preserves every raw result mass. "
                        + "The second averaging across original archive fibers uses those "
                        + "derived selection weights. Both averages stay in the same K. "
                        + "Original nodes and named action/result alphabets are unchanged. "
                        + "The derived Flow is consumed by the chronological fresh summary "
                        + "interpreter and its variable-stage realization induction."))),
                DescribeRole.Theorem))));
}
