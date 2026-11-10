using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroData;

internal sealed class ActualHeightFourteenNumericsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete Signed Zeta Resolvent Estimate",
        H("Complete Signed Zeta Resolvent Estimate"),
        Blocks(Describe.Lean(
            DescribeId.Create("actualheightfourteennumerics"),
            DeclarationHandle.Create("D5/S3/Weil/ZeroData/ActualHeightFourteenNumerics.h14_evaluatedMass_upper"),
            H("Complete Signed Zeta Resolvent Estimate"), StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The complete von Mangoldt series is split at 64. Every omitted term is retained: positive coefficients use the integral tail, and negative coefficients use nonnegativity. Rational logarithm and Euler constant bounds yield the exact signed scalar upper bound consumed by h14Mass_upper and actual_height_gt_fourteen. The first Li mass is supplied by the original owner, and no height or mass conclusion is a premise."))),
            DescribeRole.Theorem))));
}
