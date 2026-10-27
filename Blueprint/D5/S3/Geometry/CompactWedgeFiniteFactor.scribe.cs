using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class CompactWedgeFiniteFactorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/CompactWedgeFiniteFactor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compactness reduces arbitrary ordinary wedge coproduct models to actual finite selected families.",
        H("Compact finite-factor reduction"),
        Blocks(
            Node("base-points", "basePoints", "The collapsed subset",
                "For a pointed family (Z_j,b_j), take the ordinary topological sum of an additional one-point space and the dependent coproduct of all Z_j. The collapsed subset consists of the additional point and every factor basepoint. The subsetSetoid relation from FiniteConeUnionWedge identifies precisely this subset.", DescribeRole.Definition),
            Node("base", "base", "The common basepoint",
                "FamilyWedge b is the quotient by the collapsed subset, with its quotient topology. Its distinguished point is the class of the additional point. In particular an empty index type gives a point, rather than an empty space.", DescribeRole.Definition),
            Node("factor-map", "point", "Original factors map continuously into the quotient",
                "The factor map is the composition of its coproduct inclusion with the quotient projection. Each factor basepoint maps to the common basepoint.", DescribeRole.Definition),
            Node("support", "support", "Off-basepoint support",
                "The support of K consists of indices j for which some z different from b_j has its quotient class in K. One-point factors therefore contribute no off-basepoint support. Finiteness of support does not imply finiteness of the original index type.", DescribeRole.Definition),
            Node("compact-support", "compact_support", "Compact subsets meet finitely many factors away from the basepoint",
                "For arbitrary J and pointed T1 factors, every compact K in the ordinary quotient wedge has finite support. Choose one encountered nonbasepoint class p_j for each support index. These classes are distinct. For every subset E of the chosen indices, the full saturated inverse image of p(E) is empty in the additional point and has at most one point in each original factor. It is closed by T1 and the coproduct topology, so p(E) is closed by the quotient topology. If support is nonempty, the open sets complementary to p(support minus {j}) cover K. IsCompact.elim_finite_subcover gives a finite subcover, and p_j belongs only to the j-th member, forcing finite support. Empty support is immediate. No compact-subset-closed implication, Hausdorff assumption on K, closed quotient-map assumption, CW structure, or noncontractibility is used. This explicit classical compactness argument is presented as a repository derivation, without a claim of novelty or an exact literature attribution.", DescribeRole.Theorem),
            Node("include", "inclusionMap", "Inclusion of the genuine selected-family quotient",
                "For a finite F, Subwedge b F is the ordinary wedge of the unchanged factors indexed by the subtype j in F. Its continuous inclusion is constructed by the coproduct and quotient universal properties, rather than by assuming agreement of quotient and subspace topologies. F may be empty.", DescribeRole.Definition),
            Node("retract", "retract", "Retraction to the selected quotient",
                "Retain each selected factor and send every omitted factor constantly to the selected wedge basepoint. The factor maps descend continuously because all factor basepoints agree in the target. The retraction composed with inclusion is the identity. Inclusion composed with retraction fixes every subset whose off-basepoint support is contained in F.", DescribeRole.Definition),
            Node("finite-factor-data", "FiniteFactor", "Actual finite-factor data for a continuous map",
                "The source X maps continuously to Y, an arbitrary dependent coproduct of ordinary wedges. The data consist of a finite nonempty outer selection A0, a finite inner selection F_a for each retained a, and continuous maps from the concrete selected model M to Y and from Y to M. The maps satisfy r(i(m))=m and i(r(f(x)))=f(x). M is the dependent coproduct over A0 of the actual quotients of the selected original factors. An empty inner selection remains a point component.", DescribeRole.Definition),
            Node("finite-factor", "finiteFactor", "Compactness constructs the finite model and both maps",
                "For every nonempty compact X, every continuous f:X to Y and arbitrary pointed T1 factor family, finiteFactor constructs FiniteFactor b f. The native IsCompact.sigma_exists_finite_sigma_eq theorem supplies finite outer support from the compact range of f. Each outer coproduct inclusion is a closed embedding; its preimage of that compact range is compact without a Hausdorff assumption. Apply compact_support in each retained block. Include the resulting selected subwedges in their original blocks. Retract retained blocks by their wedge retractions; send every omitted outer block constantly to one chosen retained basepoint. Continuity follows blockwise from continuous_sigma_iff. Compactness and f provide a retained block because X is nonempty. All retained point components are present, including blocks with empty inner support.", DescribeRole.Definition),
            Node("finite-equivalence", "finiteFactorHomotopyEquiv", "Both inverse homotopies for the actual finite model",
                "Given an actual ordinary homotopy equivalence e:X to Y with nonempty compact X, construct the finite model using its forward map f. Its forward and backward maps are r composed with f and g composed with i. The strict equality i r f=f identifies their source composite with g f, so the supplied source inverse homotopy applies. For the target composite use J(t,m)=r(H(t,i(m))), where H is the supplied homotopy from f g to id_Y. Its endpoint is r i=id_M. Product and composition continuity suffice, and H need not remain in M. This proves an actual homotopy equivalence to the specified finite selected-family quotient model, rather than finite domination alone. Standard pointed spheres of dimension zero are retained as genuine factors. Splitting zero-spheres and conversion to positive bouquets with isolated points are separate steps; no full open-question resolution is asserted.", DescribeRole.Definition),
            Node("empty-source", "emptySourceHomotopyEquiv", "The separate empty-source model",
                "An empty source is homeomorphic, hence homotopy equivalent, to the selected model with empty outer selection. The nonempty outer conclusion of finiteFactor applies only to nonempty X.", DescribeRole.Definition))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
