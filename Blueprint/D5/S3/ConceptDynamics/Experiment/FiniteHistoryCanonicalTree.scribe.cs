using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class FiniteHistoryCanonicalTreeDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Experiment/FiniteHistoryCanonicalTree."
            + "finite_history_canonical_tree";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pointwise finite termination on a finite candidate set yields an exact "
            + "canonical passive tree preserving complete histories, labels, zero-error "
            + "singleton fibres, and rational weighted query counts.",
        H("Finite History Canonical Tree"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-history-policy-tree-correspondence"),
            DeclarationHandle.Create(Declaration),
            H("Exact finite-history policy/tree correspondence"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let W, Q, Y and L be the independent state, query, dependent "
                        + "response and terminal-label types. A readout is "
                        + "read(q) : W -> Y(q), and a deterministic policy maps every "
                        + "dependent history Hist(Y) to either a query or a terminal label. "
                        + "Execution reads one fixed state throughout, records every "
                        + "query/response pair, and may repeat queries.")),
                Paragraph(Text(
                    "For a finite candidate set C, assume only pointwise termination: "
                        + "each x in C has some fuel n, complete history t and label l "
                        + "with execute read policy n [] x = some (t,l). Then a finite "
                        + "supremum of those witnesses supplies N. Every n >= N unfolds "
                        + "the existing boundedTree operation far enough to reproduce "
                        + "each successful run exactly, with the same full history, "
                        + "length, terminal action and label.")),
                Paragraph(Text(
                    "At the reproduced history, the existing candidates predicate is "
                        + "exactly the candidates executing the same complete history "
                        + "and label at the supplied fuel. For every rational weight "
                        + "function mu and every trace/label assignment witnessed by "
                        + "successful executions on all candidates, the canonical "
                        + "weighted sum of history lengths equals the original weighted "
                        + "sum. If every completed run is decoded correctly, every "
                        + "canonical candidate fibre is a singleton and canonical "
                        + "transcripts are injective on C.")),
                Paragraph(Text(
                    "The result assumes no common input horizon, no finiteness of Q or "
                        + "the response alphabets, and no termination outside C. It "
                        + "retains repetitions and full terminal labels. In the "
                        + "circular deletion specialization it is only the generic "
                        + "finite policy prerequisite; insertion gaps, pair fibres, "
                        + "third-deletion separation and the expected-cost optimum "
                        + "remain separate results."))),
            DescribeRole.Theorem))));
}
