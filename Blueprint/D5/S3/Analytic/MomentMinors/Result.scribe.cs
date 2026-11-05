using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MomentMinors;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successive moment minors for positive probability laws.",
        H("The two moment inequalities"), Blocks(
            Describe.Lean(DescribeId.Create("moment-minors-result"),
                DeclarationHandle.Create("D5/S3/Analytic/MomentMinors/Result.result"),
                H("Both inequalities"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every interval I and every probability law on the positive reals satisfying the stated moment and logarithmic integrability conditions, both the eight-parameter inequality for phi and the displaced-parameter inequality for theta hold. All eight parameters of the first inequality belong to I. In the second inequality each of x,y,z,v and its displacement by a belongs to I.")),
                    Paragraph(Text("The midpoint moment kernel is positive semidefinite. Taking its second minors on ordered parameter pairs gives a positive semidefinite kernel whose diagonal is xi and whose off-diagonal entries are the indicated differences of xi. The two central squared moment terms have the same argument and cancel. A further second-minor construction on four parameter pairs, followed by a two by two determinant, yields the eight-parameter inequality.")),
                    Paragraph(Text("On pairs (x,x+a), the same second-minor kernel is sigma evaluated at the midpoint of the two base parameters. Its second minors have diagonal theta. Applying the same determinant argument and cancelling the two equal central sigma terms yields the displaced-parameter inequality. Repeated parameters, zero minors, and either sign of the displacement are included."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("simic-2018-iterated-moment-minor-inequalities"),
                    ResolutionKind.Proved)))));
}
