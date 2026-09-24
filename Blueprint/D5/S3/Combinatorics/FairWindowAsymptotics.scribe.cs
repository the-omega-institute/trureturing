using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class FairWindowAsymptoticsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The optimal fair-source defect has leading coefficient one and a logarithmic second-order bound.",
        H("Asymptotics of the Optimal Fair-Window Defect"),
        Blocks(Describe.Lean(
            DescribeId.Create("fair-window-asymptotics"),
            DeclarationHandle.Create(
                "D5/S3/Combinatorics/FairWindowAsymptotics.fair_window_defect_asymptotics"),
            H("Reciprocal leading term and normalized limit"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let d(R) be optimalFairDefect(R), the minimum of the exact independent "
                + "fair-source defect over all deterministic binary R-window tables, cast "
                + "from the rationals to the reals. As R tends to infinity through the "
                + "natural numbers, d(R)-1/R is O(log(R)/R^2), and R*d(R) converges to one. "
                + "Both conclusions concern this same source and this same minimum. "
                + "Choose m = 4*(floor(log base two of R+1)+1). Then 2^m is at least "
                + "(R+1)^4, m is O(log R), "
                + "and eventually m lies between one and R/2. The finite upper bound "
                + "gives d(R)-1/R at most (2m+1)/R^2. The lower bound 1/(R+2) gives "
                + "d(R)-1/R at least -2/R^2. These bounds yield the stated error order. "
                + "Finally log(R)/R tends to zero, so multiplying the error by R gives "
                + "the normalized limit."))), DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/FairWindowUpperBound")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Combinatorics/FairWindowDefect"))
        ]));
}
