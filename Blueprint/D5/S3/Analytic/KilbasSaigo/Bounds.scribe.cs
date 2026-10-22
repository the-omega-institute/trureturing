using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.KilbasSaigo;

internal sealed class BoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hyperbolic estimates from positive scaling kernels and affine differential equations.",
        H("Positivity and comparison"), Blocks(
            Paragraph(Text("A continuous function attains its minimum on each compact interval. A contraction maps that interval into itself, so the difference between its value at the contracted point and its minimum is nonnegative. A scaling equation with a strictly positive source and a nonnegative kernel therefore excludes a nonpositive minimum.")),
            Paragraph(Text("For an affine differential equation, the derivative at a positive minimizer is nonpositive in the left direction. The positive source again excludes a nonpositive minimum. Monotonicity gives the lower hyperbolic estimate. Convexity bounds each contraction difference by the endpoint chord and gives the upper estimate through the first kernel moment. The affine differential equation uses the supporting tangent at the positive endpoint for the same upper estimate.")))));
}
