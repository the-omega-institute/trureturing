using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class HyperbolicHausdorffDimensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conformal Hausdorff density in the hyperbolic upper half-space.",
        H("Hausdorff density in each natural dimension"),
        Blocks(
            Paragraph(Text(
                "Coordinates is the positive-height subtype of WithLp 2 (Complex times Real), "
                + "with its Euclidean L2 distance. Native is HyperbolicThreeSpace with distance "
                + "2 arsinh(D/(2 sqrt(hx hy))), where D is coordinate distance and hx and hy are "
                + "the two positive heights. Both spaces carry their Borel measurable structures. "
                + "The measurable equivalence coordinatesEquiv retains the underlying point.")),
            Paragraph(Text(
                "For a natural number d, rawCoordinateMeasureDim(d) and rawNativeMeasureDim(d) "
                + "denote unnormalized Hausdorff d-measure for these respective metrics. "
                + "The measurable function heightDensityDim(d) takes x to ofReal(height(x)^(-d)), "
                + "an extended nonnegative real. The ambient spaces remain three-dimensional "
                + "as d varies; d is the Hausdorff exponent.")),
            Describe.Lean(
                DescribeId.Create("raw-native-density-nat"),
                DeclarationHandle.Create("D5/S3/Geometry/HyperbolicHausdorffDimension.raw_native_density_nat"),
                H("Natural-dimensional conformal density"),
                StatementSource.FromAuthor(Disp(All("d", X("Nat"), Equal(
                    Call("map", Call("rawNativeMeasureDim", X("d")), X("coordinatesEquiv")),
                    Call("withDensity", Call("rawCoordinateMeasureDim", X("d")),
                        Call("heightDensityDim", X("d"))))))),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Geometry/sullivan1979density")),
                Blocks(
                    Paragraph(Text(
                        "The classical conformal scaling principle is described in Sullivan, "
                        + "Section 1, printed page 174: on a Borel subset of a compact manifold "
                        + "with finite positive Hausdorff mass, a continuous conformal change of "
                        + "length scale changes that mass with the Hausdorff exponent. The "
                        + "countable-partition argument below supplies the whole-half-space "
                        + "measure identity, including infinite masses, in the stated original metrics.")),
                    Paragraph(Text(
                        "The equality holds as an equality of measures for every natural d, "
                        + "without an extra finiteness or sigma-finiteness assumption. Map means "
                        + "pushforward under coordinatesEquiv. WithDensity multiplies the coordinate "
                        + "Hausdorff measure by heightDensityDim(d) through the lower integral. "
                        + "Thus both zero and infinite masses are included.")),
                    Paragraph(Text(
                        "On a Euclidean coordinate ball of radius r below the positive centre "
                        + "height h, the coordinate map and its inverse have Lipschitz constants "
                        + "h+2r and 1/(h-r). The Hausdorff image inequalities raise these constants "
                        + "to the natural exponent d. Combining them with the corresponding pointwise "
                        + "height bounds controls the weighted coordinate measure and the pushed "
                        + "native measure in both directions.")),
                    Paragraph(Text(
                        "For 0<epsilon<1, choose radius epsilon*h at each centre. The common "
                        + "comparison factor is ((1+2epsilon)/(1-epsilon))^d. These open balls "
                        + "cover the half-space. A Lindelof countable subcover, disjointified into "
                        + "Borel pieces, allows the local inequalities to be summed on every Borel "
                        + "set using countable additivity of extended nonnegative measures. "
                        + "This step requires no finite mass for a ball.")),
                    Paragraph(Text(
                        "Set epsilon(n)=1/(n+2). The comparison factors tend to one. Their products "
                        + "with each fixed extended nonnegative mass b tend to b, including b=infinity, "
                        + "because the limiting multiplier is nonzero. Closedness of the order "
                        + "relation squeezes the two measures to equality on every Borel set. "
                        + "For d=0 the height density and distortion factor are identically one.")),
                    Paragraph(Text(
                        "For d=2 the theorem supplies the height^(-2) density relative to ambient "
                        + "Euclidean-coordinate Hausdorff two-measure. It does not replace this "
                        + "measure by three-dimensional volume, and ambient Hausdorff two-measure "
                        + "is not assumed sigma-finite. Mathlib's euclideanHausdorffMeasure d "
                        + "multiplies both metric Hausdorff measures by the same dimension-dependent "
                        + "scalar; measure pushforward and withDensity commute with this scalar. "
                        + "The resulting normalized identity is independent of the separate "
                        + "three-dimensional volume calibration.")),
                    Paragraph(Text(
                        "An isometric plane chart, its original image and its coordinate Jacobian "
                        + "remain separate inputs to a surface-area change of variables. This "
                        + "ambient measure identity alone gives no triangle moment formula, "
                        + "Schlaefli variation or manifold gluing theorem."))),
                DescribeRole.Theorem)),
        []));

    private static Formula X(string name) => F.Id(name);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
}
