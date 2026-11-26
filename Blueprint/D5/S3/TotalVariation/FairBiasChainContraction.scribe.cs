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
                    "order on signed labels. The basis is the actual augmented face set. A face of " +
                    "size k has degree k minus one. The boundary deletes the vertex " +
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
                    "Take N to be one plus the maximum rank. Write h for the upward matching " +
                    "matrix and E for the unmatched part of the boundary D. Let K be the sum of " +
                    "powers of minus hE from zero through N minus one, and J the sum of powers of " +
                    "minus Eh from zero through N. With coordinate inclusion i0 and restriction " +
                    "p0, the operators are I = K i0, P = p0 J and H = K h.")),
                Paragraph(Text(
                    "The operators I and P preserve size, and H raises size by one. They obey " +
                    "PI = 1, DI = 0, PD = 0 and DH + HD = 1 - IP. A boundary cannot have a " +
                    "coefficient on a maximal face, so p0 E = 0 and P = p0. The critical " +
                    "coordinates of a cycle therefore read off the coefficients of its class " +
                    "in the cycle basis given by the columns of I."))),
            DescribeRole.Theorem))));
}
