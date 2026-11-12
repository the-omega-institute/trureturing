using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProbabilityTransport;

internal sealed class CompactKantorovichDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/atlas2026strassencoupling");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous real rectangular costs on compact probability spaces satisfy Kantorovich duality.",
        H("Compact Kantorovich duality"), Blocks(
            Describe.Lean(
                DescribeId.Create("compact-kantorovich-duality-compact"),
                DeclarationHandle.Create("D5/S3/Geometry/ProbabilityTransport/CompactKantorovich.kantorovich_duality_compact"),
                H("Equality of the real primal infimum and continuous two-potential supremum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("Let X and Y be arbitrary independently chosen nonempty compact metric spaces, each equipped with its Borel measurable structure. Let mu and nu be any Borel probability measures on X and Y, respectively, and let c from X times Y to the reals be continuous. Define P to be the set of all real integrals of c against probability measures pi on X times Y whose pushforwards by the first and second projections are exactly mu and nu. These marginal equalities use the existing CostTransport.IsCoupling relation. Define D to be the set of integral(phi,mu) + integral(psi,nu), where phi from X to the reals and psi from Y to the reals are continuous and phi(x) + psi(y) <= c(x,y) for every x and y. Then the real sInf of P equals the real sSup of D.")),
                    Paragraph(Text("The spaces can be distinct and infinite. The cost can take negative values and has no symmetry, self-zero, triangle or distance-domination assumption. Compactness makes the relevant continuous functions integrable against every probability measure. The product probability measure supplies a coupling, and a constant lower bound on c supplies a feasible potential pair. Integrating dual feasibility against any coupling gives the weak dual bound; compact bounds also justify the real infimum and supremum comparisons.")),
                    Paragraph(Text("For the reverse bound, fix epsilon > 0 and write t = sSup(D) + epsilon. On the product of the bounded continuous functions on X times Y with the reals, consider the graph of the linear map taking (phi,psi) to their pointwise sum and their marginal integral sum. The open convex set of pairs (v,r) satisfying v(x,y) - c(x,y) - (r-t) < 0 everywhere is disjoint from this graph: a compact maximum and a shift of one potential would otherwise contradict the definition of sSup(D). Geometric Hahn-Banach separation supplies a functional that annihilates the graph. Vertical rays give a nonpositive real coefficient; rays along nonnegative functions give positivity of the function component. A zero real coefficient would force the whole separator to vanish, so normalization by its strictly negative coefficient yields a positive functional L with L(phi plus psi) equal to the original marginal integral sum and L(c) <= sSup(D) + epsilon. The constant-potential test gives L(1) = 1.")),
                    Paragraph(Text("Riesz representation realizes this same positive functional as one probability measure pi on X times Y. Testing pullbacks of continuous functions along each projection and using regular-measure extensionality proves that this pi has exactly the original marginals mu and nu. The cost test identifies its integral of c with L(c). Thus its cost belongs to the original primal set and is at most sSup(D) + epsilon. Letting epsilon decrease to zero gives the reverse comparison and hence equality.")),
                    Paragraph(Text("This is the classical compact Kantorovich theorem received from the immutable ATLAS Lean formalization. The Library note identifies the exact source, license, native adaptations and scope. The theorem states equality of values; primal or dual attainment, convergence and resource bounds are not asserted."))),
                DescribeRole.Theorem))));
}
