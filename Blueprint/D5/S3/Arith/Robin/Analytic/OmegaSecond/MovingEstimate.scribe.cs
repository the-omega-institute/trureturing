using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class MovingEstimateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The moving prime remainder has a sharp upper coefficient at square-root logarithmic sharpness.",
        H("Sharp moving prime-weight upper estimate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("majorant"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.majorant"),
                H("Explicit moving-weight majorant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The majorant retains the sharp central kernel correction, the central prime-density error and both geometric tails. Each term is explicit in the real cutoff P and sharpness s."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("remainder-majorant"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.remainder_le_majorant"),
                H("Uniform finite remainder bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every sufficiently large P, every s>=pi with s>=2, and every real endpoint x, remainder(P,s,x)<=majorant(P,s). The bound is uniform in x because the omitted prime terms are nonnegative."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("majorant-limit"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.majorant_limit"),
                H("Sharp normalized majorant"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every fixed c>0, majorant(P,c*sqrt(log(P))) divided by P/(log(P)*sqrt(log(P))) tends to pi^2/(6c) as P tends to positive infinity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("moving-weight-upper"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/MovingEstimate.moving_weight_upper"),
                H("Moving prime-weight upper coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every fixed c>0 and epsilon>0, all sufficiently large P satisfy, simultaneously for every real x, remainder(P,c*sqrt(log(P)),x)<=(pi^2/(6c)+epsilon)*P/(log(P)*sqrt(log(P))). This stage proves the sharp upper coefficient used in the counting estimate. Neither an asymptotic equality for this finite remainder nor a matching lower counting bound is asserted."))),
                DescribeRole.Theorem))));
}
