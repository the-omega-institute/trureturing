using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class BoundaryObservationSplicingDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/ConceptDynamics/Gluing/BoundaryObservationSplicing.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Boundary-preserving partial splicing of dependent raw joins has an exact compatibility "
            + "domain, a single-valued observation graph, and an exact reachable image.",
        H("Boundary Observation Splicing"),
        Blocks(
            Paragraph(Text(
                "A node component A carries a dependent rawJoin record on the union of its local "
                    + "scopes. For disjoint components A and B, overlapScope is the complete variable "
                    + "carrier shared by their scopes. The left and right overlap boundaries are the "
                    + "restrictions of the two records to this same carrier. The splice assignment uses "
                    + "the left value on the left scope and the right value elsewhere; agreement on the "
                    + "overlap makes this independent of the branch.")),
            Entry("overlapScope", "shared-scope", "Shared component scope",
                "The shared variable carrier is U_A intersect U_B.", DescribeRole.Definition),
            Entry("overlapBoundaryLeft", "left-overlap-boundary", "Left overlap restriction",
                "A left record is restricted to U_A intersect U_B.", DescribeRole.Definition),
            Entry("overlapBoundaryRight", "right-overlap-boundary", "Right overlap restriction",
                "A right record is restricted to U_A intersect U_B.", DescribeRole.Definition),
            Entry("spliceAssignment", "pointwise-splice", "Pointwise partial splice",
                "For x in U_{A union B}, use a(x) when x is in U_A and b(x) otherwise. The latter branch is defined because every x in U_{A union B} lies in U_A or U_B.", DescribeRole.Definition),
            Entry("compatible_splice_unique", "compatible-splice-unique", "Unique compatible raw join",
                "For disjoint A and B, if the two complete overlap restrictions agree, the pointwise splice is a rawJoin record on A union B and is the unique rawJoin record with that value function. Empty local scopes and empty local relations remain allowed; the theorem is conditional on the displayed compatible pair.", DescribeRole.Theorem),
            Entry("compatible_overlap_transport", "compatible-overlap-transport", "Transport of initial overlap compatibility",
                "If equal local summaries preserve their corresponding complete overlap restrictions, an initially compatible pair remains compatible after both records are replaced. This is the boundary transport step used by the partial graph.", DescribeRole.Theorem),
            Entry("spliceGraph", "partial-splice-graph", "Partial observation graph",
                "The graph contains ((q_A(a),q_B(b)),q_C(a union b)) exactly for pairs whose complete overlap restrictions agree. Its domain is therefore a partial domain of summary pairs.", DescribeRole.Definition),
            Entry("spliceGraph_single_valued", "partial-splice-single-valued", "Single-valued observation graph",
                "If equal left summaries preserve the left overlap, equal right summaries preserve the right overlap, and equal summary pairs preserve the union observation after the compatible splice, then the partial graph is single-valued on its summary domain. The hypotheses are explicit so no quotient lift or representative choice is hidden.", DescribeRole.Theorem),
            Entry("spliceGraph_domain", "partial-splice-domain", "Exact compatible summary domain",
                "The graph domain is exactly the set of pairs (q_A(a),q_B(b)) with representatives whose complete overlap restrictions agree. This is an equality of sets and does not require either component relation or value family to be nonempty.", DescribeRole.Theorem),
            Entry("spliceGraph_range", "partial-splice-range", "Exact reachable union image",
                "The range of the partial graph is exactly the set of q_C observations of compatible raw pairs. Thus every reachable union observation has two local witnesses, and every compatible pair contributes a reachable observation. No global representative-selection function is asserted." , DescribeRole.Theorem))));

    private static DocumentBlock Entry(string declaration, string id, string title,
        string explanation, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);
}
