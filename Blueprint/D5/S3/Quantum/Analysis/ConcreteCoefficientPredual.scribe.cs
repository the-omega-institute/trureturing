using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class ConcreteCoefficientPredualDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Analysis/ConcreteCoefficientPredual.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restricted vector coefficients and their norm closure provide concrete normal functionals and a hereditary target for the actual posterior L1 map.",
        H("Concrete coefficient closure"),
        Blocks(
            Node("coefficient", "Actual vector coefficients",
                "For any complete complex Hilbert space H, any concrete von Neumann algebra M acting on H, and arbitrary vectors xi and eta, coefficient(M,xi,eta)(a) is the actual inner product <xi,a eta>. Its operator norm is at most ||xi|| ||eta||. All norms on the functional space are inherited from the continuous complex dual of M.", false),
            Node("coefficientSpace", "The closed complex coefficient span",
                "E is the norm closure, in the actual continuous dual of M, of the complex linear span of all restricted vector coefficients. This definition imposes neither separability nor a countable dimension condition on H. A separate theorem is required to identify this closure with the independently defined square-summable-series class; the definition itself does not establish that identification.", false),
            Node("leftTranslate", "Bounded left translation",
                "For a unital complex C-star algebra A and b in A, leftTranslate(b)(phi)(a)=phi(b-star a). It is a bounded complex-linear operator on the actual dual. The adjoint identity sends a vector coefficient to the coefficient with first vector b xi.", false),
            Node("leftTranslate_mem", "Translation preserves the coefficient closure",
                "For b in M and phi in E, leftTranslate(b)(phi) belongs to E. The adjoint coefficient identity proves invariance on the generating set. Complex linearity and the closed preimage under this bounded operator extend invariance to the entire norm closure.", true),
            Node("positive_mem_of_domination", "GNS positive heredity",
                "Let A be a unital ordered complex C-star algebra. Let E be a dual-norm closed complex submodule stable under every leftTranslate(b). If phi belongs to E and 0<=psi<=phi on every positive element, then psi belongs to E. Positivity of phi is explicit. Cauchy-Schwarz bounds psi as a functional on Mathlib's pre-GNS space of phi. Extension to its Hilbert completion and Riesz representation give a vector w. Approximate w by an algebra vector b. The functional a maps to phi(b-star a) belongs to E, and its dual-norm distance to psi is at most ||w-b|| times the pre-GNS norm of 1. This estimate includes zero mass and uses no Radon-Nikodym commutant-operator premise.", true),
            Node("coefficientSpace_hereditary", "Heredity in E",
                "The GNS heredity theorem applies to the actual coefficient closure, using its proved translation invariance. The hypothesis is membership of the dominating positive functional in E; no equivalence between intrinsic normality and a selected predual is assumed.", true),
            Node("posterior_L1_range", "The actual realized Gamma has range in E",
                "Suppose rho+sigma belongs to E and F is an actual full continuous-moment posterior family. For any continuous whole-complex-L1 map Gamma agreeing on every continuous function with linearMap(F), every Gamma(h) belongs to E. For positive continuous g, positivity gives 0<=Jg<=||g||J1, and GNS heredity puts Jg in E. Four positive parts handle all complex continuous functions. The closed preimage of E under Gamma contains the dense continuous-function image in L1, so it is the whole L1 space. The theorem applies to the exact Gamma returned by compact_normal_posterior_family. CodRestrict therefore changes only its codomain, preserving its actual values, positivity, every complex mass, contraction bound and both posterior moments; it does not manufacture another source or assume range membership.", true),
            Node("internal_lub_strong", "Internal positive directed suprema are strong limits",
                "For any nonempty directed set of positive elements of M and an M-internal least upper bound a, the vector nets converge in norm to a(v) for every v. The generalized directed-positive-net supplier constructs an ambient strong limit using only the upper bound. Every commutation identity passes to that limit by continuity on vectors. The double commutant identity puts the limit back in M. Leastness in M and in the ambient algebra then identifies it with a. No ambient least-upper-bound premise is silently substituted for the internal one.", true),
            Node("coefficient_order_normal", "Intrinsic normality of coefficients",
                "Every restricted vector coefficient is order-normal along all positive directed sets having a least upper bound internal to M. Strong convergence against the second vector implies convergence of the actual coefficient difference. The tail condition is on every element above one witness, rather than a sequential substitute.", true),
            Node("coefficientSpace_le_normalDual", "Forward normality for the entire closure",
                "All of E is contained in the intrinsic normal dual. This uses coefficient normality and the existing norm-closed complex normal-dual theorem. It proves the forward interface only, with no full converse, abstract chosen-predual identification or Sakai uniqueness assertion.", true),
            Paragraph(Text("These are classical operator-algebraic interfaces consumed by ConcreteCoefficientSeries and the standard concrete-predual reverse-test endpoint in GeneralConvexReverseTestAttainment. The former proves equality with the independently defined standard series class. The latter proves the standard-original cost equality and attainment using the same Gamma and its codRestriction. Source universes, arbitrary complex L1 inputs and extended cost conventions of the original problem are unchanged. No converse from every intrinsic-normal functional or worldwide-priority assertion is made."))
        )));

    private static DocumentBlock Node(string name, string heading, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("concrete-coefficient-predual-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(heading), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
}
