using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FairBiasSphericalWedgeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/TotalVariation/FairBiasSphericalWedge";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Collapsing the retained realization exhibits the homotopy type of the signed complex.",
        H("The sphere wedge of the signed fair-bias complex"),
        Blocks(Describe.Lean(
            DescribeId.Create("exists-spherical-wedge"),
            DeclarationHandle.Create(Module + ".exists_spherical_wedge"),
            H("The core projection and the based sphere wedge"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Suppose the signed fair-bias complex has a nonempty facet. The retained " +
                    "subcomplex collapses to the first facet's simplex and is contractible. " +
                    "The quotient map that collapses the retained realization is a homotopy equivalence.")),
                Paragraph(Text(
                    "The quotient is homeomorphic to the wedge of one standard sphere for each " +
                    "facet equal to its restriction face. Each sphere has dimension equal to the " +
                    "number of labels minus the column rank minus one. The homeomorphism " +
                    "sends the collapsed class to the wedge basepoint.")),
                Paragraph(Text(
                    "On each simplex, collapsing the entire boundary gives a sphere. In the " +
                    "singleton case the boundary is empty, and the simplex point and the added " +
                    "basepoint form a zero-sphere. The factor maps identify points on each " +
                    "boundary and identify all the boundary classes with the common basepoint. " +
                    "These are exactly the identifications of the attachment quotient. " +
                    "On each original coordinate simplex, the homeomorphism agrees with its " +
                    "sphere map followed by inclusion of the corresponding wedge factor. " +
                    "The image of the simplex together with the common basepoint covers that factor. " +
                    "If there are no such facets, the quotient is a point."))),
            DescribeRole.Theorem))));
}
