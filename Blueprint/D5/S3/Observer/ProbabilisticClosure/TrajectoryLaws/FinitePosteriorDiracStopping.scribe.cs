using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class FinitePosteriorDiracStoppingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Posterior Dirac hitting and zero-error stopping", H("Posterior Dirac hitting and zero-error stopping"),
        Blocks(
            Paragraph(Text("Let Y be a fixed target in any nonempty finite measurable label space with measurable singletons, on one probability measure mu. Let the discrete information fields form a filtration. At every radius, p is a measurable probability vector and each coordinate is a version of the conditional expectation of the actual target indicator under that same measure and field. These conditional-expectation identities are indispensable hypotheses; an arbitrary probability table is insufficient.")),
            Describe.Lean(DescribeId.Create("indicator"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePosteriorDiracStopping.indicator"),
                H("The actual target indicator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("indicator(Y,a) equals one exactly when Y=a, and zero otherwise."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("dirac-event"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePosteriorDiracStopping.diracEvent"),
                H("Finite posterior Dirac events"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("diracEvent(p,r) is the event that some label coordinate p(r,a) equals one. For a finite probability vector this is exactly the event that its maximum coordinate equals one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zero-error-iff-dirac-hitting"),
                DeclarationHandle.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePosteriorDiracStopping.zero_error_iff_dirac_hitting"),
                H("The exact finite-target stopping criterion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An almost-surely finite observable zero-error stopped classifier exists if and only if almost every sample belongs to some finite-radius diracEvent. A returned map may be infinite; the classifier is required observable on every finite return-radius and label event, is a genuine stopping time, and has zero mass of finite-return errors. Necessity integrates the actual conditional expectation on each return event: zero error implies posterior one there up to a null set. Countably many radii and finitely many labels cover every finite return. Sufficiency takes the first finite Dirac radius and selects its unique posterior-one label. Its finite return events are measurable in the corresponding information fields, and the same conditional identity proves zero error. The theorem also applies on an independent product extension whenever its posterior identities have been proved under the enlarged fields; it does not itself assume that adjoining a seed preserves a posterior."))), DescribeRole.Theorem))));
}
