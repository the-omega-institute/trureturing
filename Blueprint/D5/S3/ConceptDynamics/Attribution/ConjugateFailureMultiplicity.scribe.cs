using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ConjugateFailureMultiplicityDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/ConceptDynamics/Attribution/ConjugateFailureMultiplicity."
        + "normal_closure_loss_mul_le";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting the occurrences of each seed in distinct conjugate failure events.",
        H("Fixed mass under normal closure"),
        Blocks(Describe.Lean(
            DescribeId.Create("normal-closure-loss-mul-le"),
            DeclarationHandle.Create(Gid),
            H("Bound normal-closure loss by failure multiplicity"),
            StatementSource.FromAuthor(Bound()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let G act on a finite set S with nonnegative invariant real weights a. "
                    + "Write T for the sum of all the weights and M(K) for the weight of the "
                    + "seeds fixed by a subgroup K. Let N be the normal closure of H in G.")),
                Paragraph(Text("For each g in G, the failure event consists of the seeds moved "
                    + "by an element of the conjugate of H by g. Count each different event once "
                    + "and write r for their number. Suppose every positive-weight seed moved by N "
                    + "belongs to at least d different events, where d is a natural number.")),
                Paragraph(Text("Every event is a translate of the failure event for H. The "
                    + "sum of the weights counted over all the events therefore equals r times "
                    + "the loss for H. Counting the same weights by seed gives at least d times "
                    + "the loss for N, because each positive contribution to that loss is counted "
                    + "at least d times."))),
            DescribeRole.Theorem))));

    private static Formula Bound() => Disp(Seq(
        F.Id("d"), Sp, Open, F.Id("T"), Sp, Minus, Sp, Mass("N"), Close, Sp, Le, Sp,
        F.Id("r"), Sp, Open, F.Id("T"), Sp, Minus, Sp, Mass("H"), Close));

    private static Formula Mass(string subgroup) =>
        new Formula.FunctionCall(FormulaIdentifier.Create("M"), [F.Id(subgroup)]);
}
