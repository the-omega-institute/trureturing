using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FiniteOneStepFutureMemoryDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/Prediction/FiniteOneStepFutureMemory."
            + "finite_one_step_future_memory";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All genuine finite-state probability laws determine one-step future expectations "
            + "exactly at the one-step pullback closure, with a sharp same-V quotient bound.",
        H("Finite One-Step Future Memory"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-one-step-future-memory"),
            DeclarationHandle.Create(Declaration),
            H("All-laws one-step closure and minimal quotient memory"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state domain is finite, the action type is arbitrary, and each action "
                        + "is a fixed deterministic transition. V is the retained observation "
                        + "space and contains every constant function.")),
                Paragraph(Text(
                    "For every pair of genuine nonnegative normalized laws, agreement on all "
                        + "expectations from W implies agreement on every expectation of a "
                        + "pullback of an element of V. This statistical condition is equivalent "
                        + "to retaining V and containing all one-step pullbacks.")),
                Paragraph(Text(
                    "The closure is V plus the span of those pullbacks. Every feasible W has "
                        + "at least the closure's quotient dimension over the same embedded V, "
                        + "and the closure itself is feasible and attains equality. Empty and "
                        + "singleton state domains and an empty action family remain allowed; "
                        + "the statement is one-step and does not assert recursive invariant "
                        + "closure."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula() => Disp(Seq(
        F.Id("oneStepDetermines"), Sp, F.Id("iff"), Sp,
        F.Id("oneStepFutureClosed"), Sp, F.Id("and"), Sp,
        F.Id("quotientLowerBound"), Sp, F.Id("and"), Sp,
        F.Id("closureAttainment"), Dot));
}
