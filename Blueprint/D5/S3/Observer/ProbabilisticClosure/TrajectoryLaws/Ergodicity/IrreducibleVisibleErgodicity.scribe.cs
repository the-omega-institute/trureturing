using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.Ergodicity;

internal sealed class IrreducibleVisibleErgodicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Visible ergodicity of finite irreducible presentations", H("Visible ergodicity of finite irreducible presentations"),
        Blocks(
            Paragraph(Text("Let theta be a finite stationary binary edge-emission presentation. The output law is the visible marginal of its original integer-time joint law. Assume that the sum of its two marked matrices is irreducible.")),
            Describe.Lean(DescribeId.Create("actual-output-ergodic"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/Ergodicity/IrreducibleVisibleErgodicity.actual_output_ergodic"),
                H("Ergodicity under one-step translation"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every measurable invariant output event has versions on both observed half-lines. To construct them, approximate the event by finite cylinders, translate each approximation into the selected half-line, and use stationarity and summable errors to obtain an eventual measurable decoder.")),
                    Paragraph(Text("Conditioning at hidden state H0, the complete marked past and output future factorization forces the conditional probability k of that event to satisfy k = k squared. Positive initial state masses, derived from irreducibility and stationarity, imply k is zero or one. Thus the event indicator is a Boolean function c(H0) under the same joint law.")),
                    Paragraph(Text("Joint stationarity and event invariance imply c(H1) = c(H0) almost surely. Each positive marked edge has a positive original one-edge cylinder, so c agrees at its endpoints. Irreducible support paths connect all states, making c constant and the event null or conull. No convergence of transition powers or restriction on period is used.")),
                    Paragraph(Text("For every positive-mass actual closed hidden class, its native restricted presentation has the original marked matrix entries and is irreducible by the finite closed-class structure theorem. Applying the result gives one-step ergodicity of every such component visible law, including periodic classes."))), DescribeRole.Theorem))));
}
