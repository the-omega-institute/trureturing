using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class RandomKernelExtremumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separable overlap estimates for random label replacement.",
        H("A simplex overlap inequality"),
        Blocks(
            Paragraph(Text(
                "For a natural dimension d, set c(d,k)=(k-1)/(k(d+k-2)), "
                + "beta(d)=max of c(d,k) over 0<=k<=d, and rho(d)=(d-1)beta(d). "
                + "Real division is used, including division by zero equal to zero. "
                + "The indices zero and one contribute zero. For d>=2 this is the "
                + "same maximum as the one over 2<=k<=d.")),
            Describe.Lean(
                DescribeId.Create("simplex-overlap-bound"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/RandomKernelExtremum.simplex_overlap_bound"),
                H("All three pieces of the overlap function"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let b and a be real numbers with 0<=b<=a<=3/4, a^2<=4b, "
                    + "and a=1-(d-1)b. Suppose a<=1/n+(n-1)b for every integer "
                    + "2<=n<=d. For every nonnegative real vector s on Fin d with "
                    + "sum one, the sum of (1-s(i))min(b,s(i))+s(i)min(a,s(i)) "
                    + "is at least a.")),
                    Paragraph(Text(
                    "If a coordinate is at least a, its overlap contributes an extra b "
                    + "above the linear bound (a-b)s(i). The discriminant condition "
                    + "gives that linear bound on the middle interval. Otherwise, split "
                    + "the coordinates at b. Cauchy-Schwarz on the middle coordinates "
                    + "and the finite support inequalities give the estimate; zero "
                    + "and one middle coordinate are handled separately."))),
                DescribeRole.Theorem))));
}
