using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Trajectories;

internal sealed class GeometricMaximumTiesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact tied-maximum series and reciprocal size bound for independent geometric samples.",
        H("Tied Maxima of Independent Geometric Samples"),
        Blocks(Describe.Lean(
            DescribeId.Create("tied-maximum-bound"),
            DeclarationHandle.Create(
                "D5/S3/ObserverMemory/Trajectories/GeometricMaximumTies.tied_maximum_bound"),
            H("The full probability of attaining a maximum"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let 0<p<1 and let X(0),...,X(n) be mutually independent measurable "
                        + "natural-valued variables on any probability space. Each has singleton "
                        + "mass (1-p)p^j at j. The event considered is X(i)<=X(0) for every "
                        + "i=1,...,n, so every tie is included. Adding one to each variable gives "
                        + "the positive geometric lengths with mass (1-p)p^(z-1) at z>=1.")),
                Paragraph(Text(
                    "The theorem identifies the event probability with the convergent series "
                        + "whose j-th term is (1-p)p^j(1-p^(j+1))^n, and bounds that probability "
                        + "by (1-(1-p)^(n+1))/(p(n+1)) and by 1/(p(n+1)). There are n+1 samples. "
                        + "At n=0 the comparison is empty, the event is the whole space, and the "
                        + "stronger bound equals one.")),
                Paragraph(Text(
                    "Partition the event according to X(0)=j. Summing singleton masses gives "
                        + "Pr(X(i)<=j)=1-p^(j+1), and mutual independence gives each partition "
                        + "piece its stated mass. Countable additivity gives the convergent series.")),
                Paragraph(Text(
                    "Put a(j)=1-p^(j+1). The difference a(j+1)-a(j) is p(1-p)p^j. "
                        + "Bernoulli's inequality bounds p(n+1) times the j-th series term by "
                        + "a(j+1)^(n+1)-a(j)^(n+1). These differences telescope; a(j)<=1 and "
                        + "a(0)=1-p give the stronger bound after passage to the convergent sum. "
                        + "This is the discrete power-difference form of comparison on the "
                        + "geometric partition intervals [p^(j+1),p^j]."))),
            DescribeRole.Theorem))));
}
