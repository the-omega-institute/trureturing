using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class SingleLengthBandGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/SingleLengthBandGeometry.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial bands retain the integer range and logarithmic bounds for single-length moments.",
        H("Single-length band geometry"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("band-geometry"),
                DeclarationHandle.Create(Prefix + "band_geometry"),
                H("Integer cutoff and length ranges"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix 0<alpha<beta<1/4. For all sufficiently large Y, uniformly over Y^alpha<=v<=Y^beta, let N and K be the natural floors of Y and v. Then N>=2, K>=1, N>=Y/2, K>=v/2, Y^(alpha/2)<=K<=Y^beta, K<=2*N^beta, and log N<=K<=N^(1/4). The doubled band permits the integer moment estimate to use the same exponent beta after flooring the cutoff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("band-log"),
                DeclarationHandle.Create(Prefix + "band_log"),
                H("Uniform logarithmic comparison"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If beta<1, Y>1, and 1<=v<=Y^beta, then log(Y/v) is positive and lies between (1-beta)*log Y and log Y. The lower bound holds with the same positive factor 1-beta throughout the length band."))),
                DescribeRole.Theorem))));
}
