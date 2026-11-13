using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.AlgebraicBoundary;

internal sealed class BoundaryCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constructed transverse polynomial coordinates.",
        H("Constructed transverse polynomial coordinates."),
        Blocks(
            Paragraph(Text("Every nonzero vector e in a finite real coordinate carrier admits an actual invertible continuous linear coordinate map. Choose a coordinate i with e(i) nonzero and put u(x)=x(i)/e(i). The transverse coordinates are pi(x)(j)=x(j)-e(j)u(x) for j different from i. Their section J inserts zero at i. Thus u(e)=1, pi(e)=0, u(Jv)=0, pi(Jv)=v and x=u(x)e+J(pi(x)). The construction also applies when the transverse index type is empty.")),
            Paragraph(Text("Substitution by this coordinate map is a polynomial ring equivalence. Its inverse is substitution by the actual inverse linear map, certified by polynomial function extensionality. Polynomial evaluation is preserved on every original ambient vector. BoundaryPrincipalIdeal consumes the equivalence and its evaluation identity to transport irreducible factors, arbitrary comparison equations and their exact divisibility back to the original coordinates. No chart or factorization is assumed as an input.")))));
}
