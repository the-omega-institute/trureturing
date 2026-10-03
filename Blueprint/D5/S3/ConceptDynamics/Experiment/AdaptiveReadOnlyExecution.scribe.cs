using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Experiment;

internal sealed class AdaptiveReadOnlyExecutionDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Experiment/AdaptiveReadOnlyExecution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adaptive read-only controllers retain dependent responses and charge distinct queries.",
        H("Adaptive Read-Only Execution"),
        Blocks(
            Definition("controller", "Controller", "History controller",
                "The existing Hist(Y) carrier is a finite list of dependent query-response pairs. "
                    + "A controller maps only this record to an optional sum of a query action "
                    + "and a return value. None denotes a stall. Source, action, dependent "
                    + "response, and return types are arbitrary; no finiteness is required."),
            Definition("consistent", "Consistent", "History consistency",
                "Each recorded dependent response equals read(a,x) for the same fixed source x. "
                    + "Queries read the source without changing it."),
            Definition("queries", "queries", "Distinct query set",
                "Mapping the history to its actions and taking toFinset retains exactly the "
                    + "distinct queries. This definition requires decidable equality on actions."),
            Definition("query-count", "queryCount", "Distinct query count",
                "The charge is the cardinality of the distinct query set. Repeated queries "
                    + "are allowed and contribute no additional charge."),
            Definition("run", "Run", "Finite execution relation",
                "Run(read,pi,x,pre,t,b) retains the additional ordered record t after prefix pre "
                    + "and returns b. Its stop constructor records an immediate return; its query "
                    + "constructor appends the actual dependent response before continuing. "
                    + "There is no fuel or height bound and no constructor for a stall. "
                    + "The controller observes only the preceding record."),
            Definition("correct", "Correct", "Total finite correctness",
                "For every source x there exists a finite run from the empty history returning "
                    + "target(x). This imposes no uniform bound on finite execution lengths."),
            Definition("cost", "cost", "Extended execution cost",
                "Cost takes the extended nonnegative infimum of distinct-query counts over all "
                    + "finite run witnesses and return values. With no finite witness the "
                    + "infimum is top, including stalled and infinite query executions."))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        string description) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(DeclarationPrefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))),
            DescribeRole.Definition);
}
