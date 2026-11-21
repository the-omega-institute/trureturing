using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class FairBiasIntegralHomologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full-restriction facets index a basis for the only possible nonzero reduced homology group.",
        H("Reduced integral homology of the signed fair-bias complex"),
        Blocks(Describe.Lean(
            DescribeId.Create("reduced-homology-eq-full-restriction-facets"),
            DeclarationHandle.Create(
                "D5/S3/TotalVariation/FairBiasIntegralHomology.reducedHomology_eq_fullRestrictionFacets"),
            H("Homology of the original realization in every nonnegative degree"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Geometry/hatcher2002algebraic")),
            Blocks(
                Paragraph(Text(
                    "Take a finite family of columns in a finite binary vector space and fix a linear " +
                    "order on the signed labels. The signed fair-bias complex has free reduced " +
                    "integral singular homology in " +
                    "column nullity minus one, using natural subtraction. The summands are indexed " +
                    "by the facets equal to their restriction faces. Every other nonnegative degree " +
                    "vanishes. If there are no nonempty facets, the realization and index are empty, " +
                    "so every nonnegative degree vanishes.")),
                Paragraph(Text(
                    "When a facet exists, the core quotient carries the homology of the original realization to its " +
                    "sphere wedge. For positive degrees, a based homeomorphism separates one factor " +
                    "from the wedge of the remaining factors. Stereographic projection gives contractions " +
                    "fixed at their basepoints, and the binary Mayer–Vietoris splitting adds one " +
                    "summand at each step, as in Hatcher’s wedge-sum argument in Corollary 2.25. " +
                    "A sphere contributes its coefficient group only in its own degree.")),
                Paragraph(Text(
                    "In degree zero, a positive-dimensional sphere wedge is path connected. A " +
                    "wedge of zero-spheres has one point for each factor in addition to the common " +
                    "point. The augmentation kernel has one generator for each of those other " +
                    "components. An empty family gives a point and every reduced group vanishes."))),
            DescribeRole.Theorem))));
}
