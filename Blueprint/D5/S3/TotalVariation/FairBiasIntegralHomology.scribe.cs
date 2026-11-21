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
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Geometry/hatcher2002algebraic")),
            Blocks(
                Paragraph(Text(
                    "Suppose the signed fair-bias complex has a nonempty facet. Its reduced " +
                    "integral singular homology in the degree given by the number of labels " +
                    "minus the column rank minus one is a free abelian group indexed by the " +
                    "facets equal to their restriction faces. Every other nonnegative degree vanishes.")),
                Paragraph(Text(
                    "The core quotient carries the homology of the original realization to its " +
                    "sphere wedge. For positive degrees, a based homeomorphism separates one factor " +
                    "from the wedge of the remaining factors. The punctured spheres have contractions " +
                    "fixed at their basepoints, and the binary Mayer–Vietoris splitting adds one " +
                    "summand at each step. A sphere contributes its coefficient group only in its own degree.")),
                Paragraph(Text(
                    "In degree zero, a positive-dimensional sphere wedge is path connected. A " +
                    "wedge of zero-spheres has one point for each factor in addition to the common " +
                    "point. The augmentation kernel has one generator for each of those other " +
                    "components. An empty family gives a point and every reduced group vanishes."))),
            DescribeRole.Theorem))));
}
