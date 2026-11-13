using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;
internal sealed class ConeFiniteBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original principal boundary ideal at arbitrary finite degree.",
        H("Arbitrary-degree entire boundary minima"),
        Blocks(Paragraph(Text("Any nonzero polynomial vanishing on the entire original ambient frontier gives native semialgebraicity. Directly consume exists_homogeneous_minimum and minimum_boundary_ideal on the original coordinate image. This gives a positive minimum degree, a homogeneous squarefree nonzero equation of exactly that degree, and divisibility of every original entire-boundary equation, with no degree or homogeneity restriction on the comparison equation. Both directions of the principal ideal identity are retained.")),
        Paragraph(Text("Every nonzero comparison equation of at most the minimum degree is a scalar multiple of that same generator: divide it by the generator using the actual ideal theorem, then use additivity of total degree in the polynomial domain. The quotient has degree zero and hence is a real constant; nonzero comparison excludes a zero constant. This arbitrary-degree scalar uniqueness uses no interior nonvanishing or hyperbolicity premise. These exact-owner applications are consumed by the full host and contribute no separate escape credit.")))));
}
