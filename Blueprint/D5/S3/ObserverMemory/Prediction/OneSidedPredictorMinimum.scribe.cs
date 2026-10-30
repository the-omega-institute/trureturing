using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class OneSidedPredictorMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp one-sided predictive memory.", H("Sharp one-sided predictive memory"), Blocks(
            Describe.Lean(DescribeId.Create("sharp-predictor-minimum"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/OneSidedPredictorMinimum.sharp_predictor_minimum"),
                H("Sharp one-sided predictive memory"), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A predictor has one fixed initial state, a total update receiving one Boolean outcome, and an output in the closed interval from zero to one. Its reached state is the left-to-right runWord fold. Every persistent counter, program phase and parse state belongs to this carrier; no time or source-state argument is supplied.")),
                    Paragraph(Text("Let x lie in (0,1], let epsilon be nonnegative with 2 epsilon < x, and let p be a nonnegative decreasing sequence bounded above by x and tending to zero. The history law is x once a false outcome has occurred, and otherwise p evaluated at the history length. Correctness requires absolute next-outcome error at most epsilon for every finite Boolean history, including the empty history.")),
                    Paragraph(Text("Suppose N is the first nonstrict threshold: p(n) <= 2 epsilon if and only if N <= n. There is a correct predictor on Fin(N+1) + Unit, whose cardinality is N+2, and every correct predictor on any finite carrier has at least N+2 states.")),
                    Paragraph(Text("The Fin states store the all-one depth up to N. The last one saturates and outputs p(N)/2; the Unit state records that a zero has occurred and outputs x. The saturation error is at most p(N)/2. This includes N=0 and exact threshold equality.")),
                    Paragraph(Text("If two distinct all-one depths reach the same state, deterministic continuation repeats the earlier state along an unbounded arithmetic progression. Taking the limit of its error inequality forces the earlier p value to be at most 2 epsilon. Thus the first N+1 all-one states are distinct. A zero-history state cannot equal any of them: a common all-one suffix would require one output to approximate both x and a sequence tending to zero.")),
                    Paragraph(Text("This theorem concerns a specified history law. Applying it to a retained quantum instrument requires deriving that law from the actual branches. It counts persistent states; output installation precision and computation time are separate resources."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-prediction-impossible"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/OneSidedPredictorMinimum.exact_prediction_impossible"),
                H("Exact prediction needs infinitely many states"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If every p(n) is strictly positive and p tends to zero, every finite carrier fails exact all-history prediction, for any reset output x. Pigeonhole gives a repeated all-one state; its deterministic recurrence and the limit force the earlier strictly positive p value to be zero."))),
                DescribeRole.Theorem))));
}
