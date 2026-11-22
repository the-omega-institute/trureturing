using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReflectingHeatDirectionalBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reflecting heat interpolant satisfies contour estimates at the prescribed half-width.", H("Directional growth of the reflecting heat interpolant"),
        Blocks(
            Describe.Lean(DescribeId.Create("reflecting-heat-directional-bound-moment-interpolant-contour-bounds"),
                DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatDirectionalBound.momentInterpolant_contour_bounds"),
                H("Half-width estimate and moment nodes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An entire multiplier with radial half-width L/2, polynomial order m, and the Joukowski real-axis envelope produces an entire interpolant. Bounding the n minus two omitted polynomial factors gives order n minus two plus m. On the real axis the Joukowski powers cancel up to one inverse radius, and the remaining square root bounds both the positive mode rate and the absolute frequency. The directional estimate therefore uses exp((L/2) |Im z|) with the same polynomial order. The real restriction has the squared-norm bound from the interpolation theorem. At the Fourier moment nodes minus i times the mode rates the interpolant vanishes off the target mode. Its target value is the nodal derivative times the multiplier evaluated at that node."))),
                DescribeRole.Theorem))));
}
