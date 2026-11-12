using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FacetZeroGluingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole-base facet injection from original mixed-state zero gluing.",
        H("Whole-base facet injection from original mixed-state zero gluing"),
        Blocks(
            Paragraph(Text("The source is Quantum Origin: Finite Pure Point and Facet Obstructions VII, Theorem 96.2, with the entire original carrier and definitions from VI 89.1 and V 88.1–88.3. This is distinct from VI Chapter 96. The real finite dimensional normed carrier, original cone and strictly positive linear unit determine the entire normalized base, all its extreme points and all original proper effects. Finiteness applies to that complete extreme-point set. No ball, antipodal separation, reciprocal comparison, least effect, selfdual pairing or supplied exposure is assumed.")),
            Describe.Lean(DescribeId.Create("exclusion"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FacetZeroGluing.exclusion"),
                H("All original mixed-state exclusions"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For the original p, the exclusion set consists exactly of normalized original x for which some linear functional f is proper on every vector of the entire original cone, has f(p)=1 and f(x)=0. The confirming and zero readings belong to the same effect. The zeroGluing premise is the original full mixed-state midpoint condition owned by WeightedRelationConfirmation."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("facets"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FacetZeroGluing.facets"),
                H("Native facets of the whole base"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("A facet is a native PointedCone.Face of the entire original cone whose real linear span has codimension one in the original carrier. Its whole normalized slice uses the original unit. The main theorem proves that each slice is convex and a native extreme subset of the whole original base, and that its affine dimension plus two equals the dimension of the original carrier. Thus for m=dim(V)-1 its slice has dimension m-1. The theorem assumes dim(V)>=2, exactly the source branch m>=1; the single-point m=0 branch is excluded from facet selection."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("common-effect"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FacetZeroGluing.zero_gluing_common_effect"),
                H("One original effect for the entire exclusion set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("On any original finite dimensional carrier, original mixed-state Z0 and nonemptiness of D_p imply existence of one original proper confirmer f with D_p equal to the normalized base intersected with ker(f). This requires neither finite pure points nor a least confirmer. A finite spanning subset of D_p is chosen using Mathlib. Repeated mixed-state midpoints construct a point whose zero reading forces every chosen reading to vanish, by nonnegativity. Applying Z0 along this construction supplies a confirmer vanishing on the spanning subset and hence on all of D_p. The reverse containment uses that very confirmer as the original exclusion witness. This is the common-exposure predecessor from V 88.3, derived without compactness or an exposure input."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("whole-facet-injection"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FacetZeroGluing.whole_facet_injection"),
                H("All native facets inject into all original pure points"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume the original cone is closed and generating, its unit is strictly positive away from zero, all original pure points form a finite set, dim(V)>=2, and the original mixed-state Z0 holds. Every native facet F has an original pure p with D_p equal to the entire normalized slice of F and p outside F. Any function choosing such a p for every facet is injective. The complete native facet type has cardinality at most the complete original pure type. For every pair F,G, the chosen p_G lies in F if and only if the chosen p_F lies in G. No global surjection or polarity of the face lattice follows.")),
                    Paragraph(Text("The support construction uses the native cone-face property to prove C intersect span(F)=F. A nonzero functional annihilating the codimension-one span is oriented using an original cone vector. A negative reading at another cone vector would yield a positive conic combination in F, forcing the first vector into F and contradicting its positive reading. Maximization ranges over all original pure points, and the normalized support is extended to every original cone vector by the existing cone_bound theorem. The common zero effect has the same codimension-one kernel. Equality of exclusion sets identifies equal choices with equal whole native faces. Complements u-f establish the cross-incidence symmetry, without assuming reciprocity at nonzero comparison values.")),
                    Paragraph(Text("The finite-pure coordinate and cone infrastructure integrated from the pinned WeightedRelationConfirmation dependency is prior work. The new mathematical construction is the universal finite zero-test induction, its whole-exclusion consequence and the native facet support and kernel argument. The dimension and whole-face clauses are mathematical consequences within the stated original model. They supply no preparation program, physical effect supplier, new cone classification or physical-source bridge. VII 96.3–96.5 remain outside this result; literature priority is not asserted."))), DescribeRole.Theorem))));
}
