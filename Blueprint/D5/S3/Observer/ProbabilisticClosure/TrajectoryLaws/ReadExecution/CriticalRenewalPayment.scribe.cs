using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class CriticalRenewalPaymentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact price of a stopped prefix of actual renewal gaps.",
        H("Critical renewal payment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("criticalrenewalpayment-actual-source-payment"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/CriticalRenewalPayment.actual_source_payment"),
                H("Exact paid means on the same execution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural r at least one, positive real c and s, positive natural H, natural J and one immutable Tick J, use the two gapLaw and waitLaw probability mass functions of CriticalRenewalSource. For each label separately, assume almost-sure finiteness of gapStop and integrability of its real natural-value projection under sourceLaw. Then paidStop is almost surely finite and its real natural-value projection is integrable under that same law. Its expectation is exactly one plus beta plus mean times the expectation of the natural-value projection of gapStop. The Tick argument precedes the label quantifier, so both conclusions concern the same table.")),
                    Paragraph(Text("The zero-indexed block n is undertaken exactly when all evidence prefixes through n remain strictly between the integer thresholds. This event uses only the first n duration-mark pairs. The next duration is the first coordinate of pair n. The independent-pair law fresh_same_source therefore factors the expected included duration into its actual cycle mean times the inclusion probability. No factorization separates a duration from its own phase or tick increment, or from the decision after its closing tick.")),
                    Paragraph(Text("The included duration is the number of zeros in that very block plus one. Nonnegative summation exchanges expectation and the series of included durations. On each finite exit path, stopped_prefix_payment identifies their sum with the uninterrupted consecutive-bit execution. Its initial contribution is the equilibrium wait plus the first tick; every zero after phase death and the final closing tick is charged. The first wait has the derived equilibrium distribution rather than the iid gap distribution.")),
                    Paragraph(Text("The stopping times retain their infinite value on nonterminating paths. Natural-value projections are used only after almost-sure gap exit is supplied. The source moments and equilibrium wait expectation are derived by source_laws. The payment argument requires neither independence of gapStop and durations nor a source reset. Numerical gap-exit and risk estimates require separate drift and moment bounds for this same table and source."))),
                DescribeRole.Theorem))));
}
