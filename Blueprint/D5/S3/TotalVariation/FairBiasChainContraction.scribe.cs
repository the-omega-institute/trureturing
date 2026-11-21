using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FairBiasChainContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit integral contraction of the augmented signed fair-bias chains.",
        H("Cycle representatives of the signed fair-bias complex"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-contraction"),
            DeclarationHandle.Create(
                "D5/S3/TotalVariation/FairBiasChainContraction.actualContraction"),
            H("The augmented chains retract onto the full-restriction facets"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a finite binary column family with a nonempty signed facet and a linear " +
                    "order on signed labels. The basis is the actual augmented face set. A label of " +
                    "size k represents a face in degree k minus one. The boundary deletes the vertex " +
                    "in position j with coefficient minus one to the power j, counting from zero. " +
                    "In particular, a singleton maps to the empty face with coefficient one.")),
                Paragraph(Text(
                    "Deleting any two distinct vertices in opposite orders gives the same subface " +
                    "with opposite coefficients. This proves square zero, including the composition " +
                    "that ends in degree minus one. A cover has a unique deleted vertex. Its " +
                    "incidence coefficient is an integer unit and equals its own inverse.")),
                Paragraph(Text(
                    "Use one pivot per nonsingleton restriction interval, including the interval of " +
                    "the empty face. The fixed points are exactly the full-restriction facets. " +
                    "The rank decreases on unmatched downward and matched upward edges, so the " +
                    "finite cancellation applies to the signed boundary. The critical coordinates " +
                    "have size equal to the column nullity and the transferred differential is zero.")),
                Paragraph(Text(
                    "The corrected inclusion and projection keep size, and the homotopy raises size " +
                    "by one. The projection composed with the inclusion is the identity. Each " +
                    "included generator has its original coefficients on the critical faces. The two " +
                    "composites with the boundary give the chain identities and the homotopy identifies " +
                    "the other composite with the identity. A nonempty facet supplies the partner " +
                    "of the empty face. With no nonempty facet the augmented complex contains a " +
                    "single basis element in degree minus one and its differential is zero."))),
            DescribeRole.Theorem))));
}
