using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport;

internal sealed class PathRatioBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/DivergenceSupport/PathRatioBound",
            "The path contraction ratio is a weighted average of pointwise ratios and is bounded by their path supremum."),
        H("Weighted Path-Ratio Bound"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("path-ratio-weighted-average-and-supremum-bound"),
                H("Path contraction is a weighted average bounded by the path supremum"),
                LeanTheorem(
                    "D5/S3/DivergenceSupport/PathRatioBound.path_ratio_weighted_average_and_bound"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Frac,
                    Grp(Operatorname, Grp(F.Id("targetPath")), Open, F.Id("d"), Close),
                    Grp(Operatorname, Grp(F.Id("sourcePath")), Open, F.Id("d"), Close),
                    Eq,
                    Operatorname, Grp(F.Id("weightedAverage")),
                    Underscore, Grp(F.Id("d")), Open,
                    Operatorname, Grp(F.Id("pointwiseRatio")), Close,
                    Comma, RowBreak,
                    Operatorname, Grp(F.Id("targetPath")), Open, F.Id("d"), Close,
                    Le,
                    Operatorname, Grp(F.Id("pathSup")), Open, F.Id("d"), Close,
                    Operatorname, Grp(F.Id("sourcePath")), Open, F.Id("d"), Close,
                    Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let the input squared path speed be strictly positive on the unit " +
                        "interval. Assume the source weight and its product with the " +
                        "pointwise output-to-input speed ratio are interval integrable, the " +
                        "source path integral is positive, and the pointwise ratios are " +
                        "bounded above.")),
                    Paragraph(Text(
                        "The output path integral equals the integral of pointwiseRatio times " +
                        "pathWeight. After division by sourcePath, this is the weighted average " +
                        "displayed above, with normalized weight pathWeight divided by " +
                        "sourcePath. Pointwise domination by pathSup and nonnegativity of the " +
                        "path weight give targetPath(d) <= pathSup(d) * sourcePath(d).")))))));
}
