using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class GNSOrderCoordinatesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/GNSOrderCoordinates.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classical order-Radon--Nikodym coordinates in the actual completed GNS of a positive functional on an arbitrary unital complex C-star algebra.",
        H("Positive commutant coordinates from GNS comparison"),
        Blocks(
            Paragraph(Text("Let A be a unital complex C-star algebra with a compatible star order. The positive complex-linear functional psi is arbitrary: it need not be faithful, normalized or nonzero. Its GNS Hilbert space, representation pi and pre-GNS maps are the ones constructed by Mathlib. Omega is the image of the unit, without normalization. No separability, finite-dimensionality or countability assumption is used.")),
            Node("comparison_norm_le", "The canonical comparison contraction",
                "For positive complex-linear functionals phi and psi, suppose phi(a)<=psi(a) for every positive a. Sending psi.toPreGNS(a) to phi.toPreGNS(a) is complex linear and decreases the pre-GNS seminorm, since the squared norms are phi(a* a) and psi(a* a). Completing this map gives J: GNS(psi) to GNS(phi) with operator norm at most one. Completion accounts for null vectors, including the zero Hilbert space."),
            Node("comparison_intertwines", "Intertwining the actual representations",
                "For every a in A, J pi_psi(a)=pi_phi(a) J. This equality holds first on each pre-GNS vector by associativity of left multiplication and then on the whole completion by density and continuity. The image under J of the unnormalized cyclic vector for psi is the cyclic vector for phi."),
            Node("comparison_adjoint_intertwines", "Adjoint intertwining",
                "Taking adjoints of the intertwining identity at a* gives J* pi_phi(a)=pi_psi(a) J*. Both representations are the actual star homomorphisms supplied by the completed GNS construction."),
            Node("coordinate_mem", "A constructed positive commutant contraction",
                "Set T=J*J. Then 0<=T<=I in the usual Loewner order on bounded Hilbert-space operators, and T commutes with pi_psi(a) for every a in A. Positivity is the adjoint-square theorem; the upper bound follows from the contraction estimate on all vectors; commutation follows from both intertwining identities."),
            Node("coordinate_represents", "Exact coefficient of the original functional",
                "For every a in A, phi(a)=<Omega,T pi_psi(a) Omega>. More generally the coefficient between the pre-GNS images of a and b is phi(a* b). Thus T represents the given functional itself, including every singular input allowed by domination."),
            Node("coefficient_injective", "Uniqueness on the full commutant",
                "For any two bounded operators T and S commuting with pi_psi(A), equality of their complex-linear coefficient functionals implies T=S. Neither operator needs to be positive or self-adjoint. Apply the existing cyclic Schur lemma to T-S and scalar zero, using the actual dense GNS orbit. That library theorem proves uniqueness by off-diagonal matrix coefficients and density."),
            Node("coefficient_nonneg_iff", "Positivity reflects through the cyclic coefficient",
                "For any bounded commutant operator T, the coefficient is nonnegative on all positive elements of A if and only if T is positive in the Loewner order. In the reverse direction its quadratic form is nonnegative on the dense pre-GNS range, hence everywhere by continuity. The complex polarization criterion supplies self-adjointness; it is not assumed separately."),
            Node("coefficient_order_iff", "Preservation and reflection of order",
                "For arbitrary bounded commutant operators T and S, coefficient_T(a)<=coefficient_S(a) for every positive a if and only if T<=S. Apply positivity reflection to S-T. This is the actual positive-cone order on functionals and the usual operator order, with no change of order relation."),
            Node("existsUnique_coordinate", "The actual order-Radon--Nikodym existence theorem",
                "Every positive complex-linear phi dominated by psi on the positive cone has exactly one bounded operator T such that 0<=T<=I, T commutes with every pi_psi(a), and its coefficient functional is exactly phi. Existence uses the canonical J*J construction; uniqueness uses density. Conversely any positive commutant contraction defines a positive complex-linear functional dominated by psi by the same coefficient formula."),
            Definition("orderCoordinates", "The constructed order isomorphism",
                "DominatedFunctional(psi) is the subtype of Mathlib positive complex-linear functionals dominated by psi on positive elements. CommutantInterval(psi) is the subtype of bounded operators satisfying 0<=T<=I and commuting with every pi_psi(a). The map orderCoordinates is an actual order isomorphism between these two types: its forward map is J*J, its inverse is the coefficient functional, both composites are identities, and order comparison agrees in both directions. Antisymmetry of functional order uses the fact that positive elements span the complex C-star algebra."),
            Node("original_pair_coordinate", "Coordinates for the original prescribed positive dual inputs",
                "Let rho and sigma be arbitrary continuous complex-linear functionals nonnegative on positive elements. Convert rho+sigma to its actual positive-linear-map GNS input without changing any value. There exists exactly one positive commutant contraction C whose coefficient is rho and whose complementary operator I-C has coefficient sigma, as equalities of complex-linear functionals. This includes singular rho and sigma, the zero input pair and nonnormalized masses. No normality assumption is needed for this more general existence statement."),
            Paragraph(Text("For an order-normal psi, the existing NormalFunctionals.isOrderNormal_of_domination theorem applies directly to the inverse order coordinate, using 0<=eta_T<=psi. Its conclusion uses precisely the arbitrary-directed order-normality predicate; it does not identify order-normality with an independently defined coefficient-series predual.")),
            Paragraph(Text("These are classical foundational operator-algebra results, expressed using Mathlib's actual GNS spaces and completion API. The continuous coefficient functional, its evaluation on a* a, and the cyclic Schur lemma are reused from the Physicslib4 suppliers in IrreducibleBoundedLift. They supply order coordinates for the pending arbitrary-von-Neumann full-curvature maximal-hockey versus maximal-f classification. They do not establish normality of the GNS representation, the compressed centralizer criterion, full-curvature necessity, or realization of all reverse tests on the entire complex L1 space. In particular the required centralization concerns the open spectral corner PNP and cannot be replaced by global commutation."))
        )));

    private static DocumentBlock Node(string name, string heading, string prose) =>
        Describe.Lean(DescribeId.Create("gns-order-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string name, string heading, string prose) =>
        Describe.Lean(DescribeId.Create("gns-order-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
