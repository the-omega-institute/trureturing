using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSQ2PolynomialFiberDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSQ2PolynomialFiber";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact polynomial Q2 observations and fibers through every certified canonical parameter.",
        H("Raw prefix observations on the canonical parameter domain"),
        Blocks(
            Item("coordinates", "positiveRepresentative", "Thirteen real coordinates and their positive representative",
                "Coordinates 0 through 4 are the real parts of the five complex canonical core entries c0 through c4; coordinates 5 through 9 are their imaginary parts. Coordinate 10 is sigma, and coordinates 11 and 12 are the real and imaginary parts of eta. The old Parameter has different boundary coordinates q0 and q1. The positive representative is exactly (c,sqrt(sigma),sqrt(sigma)*eta). It is continuous, and injective when sigma is positive. Every old parameter with q0 positive is represented by sigma=q0 squared and eta=q1/q0. The square root occurs only in this representative. Positive amplitude scale is retained.",
                DescribeRole.Definition),
            Item("gram-transfer", "q2Polynomial", "A polynomial transfer observation",
                "All polynomials have complex coefficients and thirteen real input variables. Coefficient conjugation fixes the variables. The two core matrices and the left row are the original canonical formulas. The boundary Gram is sigma times the matrix with rows (1,conjugate eta) and (eta,eta times conjugate eta); in particular the 10 entry is sigma times eta. Form the prefix row with only the fixed two-site product L A(u0) A(u1). Iterate the two by two transfer T(H)=sum_s A_s H A_s dagger m times on this Gram and sandwich by the fixed prefix and its adjoint. No full-length word expansion, trace normalization or trace-preservation assumption is used.",
                DescribeRole.Definition),
            Item("polynomial-evaluation", "q2Polynomial_eval", "Exact equality with the existing raw density",
                "For every natural complement length m and every real coordinate vector x with sigma(x) nonnegative, evaluating the polynomial matrix equals the existing density m of positiveRepresentative x, namely rawPrefix 2 m of its actual length 2+m MPS state. Evaluation commutes with coefficient conjugation, matrix products and the transfer iterate. The boundary identity uses the square of sqrt(sigma) equal to sigma. The proof directly consumes density_factor; it introduces no second transfer, Gram-rank or Schur-completion proof. The equality also holds at m=0, without asserting a nonempty leading-invertible chart at that length.",
                DescribeRole.Theorem),
            Item("record-evaluation", "recordPolynomial_eval", "The existing twelve real record components",
                "recordEquiv is an explicit equivalence from the old Record to Fin 12 real coordinates. The order is the two leading diagonal real entries, real and imaginary parts of its off-diagonal entry, then real and imaginary pairs for B00, B01, B10 and B11 in the upper-right block. Applying the existing realCoeff, imagCoeff and coefficient_eval gives the exact packed old record, for every m and sigma nonnegative. Record equality is lifted to equality of the entire raw Q2 by the unchanged densityRecord_injective on the leading-invertible chart, consuming the original density Hermitian and rank bounds.",
                DescribeRole.Theorem),
            Item("generic-fiber", "exists_generic_fiber", "Fibers through each certified parameter in every neighborhood",
                "For each k, let O be the set where sigma is positive and the positive representative belongs to the old canonicalChart k. O is open and nonempty, by continuity, the old canonicalChart_nonempty and transport with sigma=q0 squared and eta=q1/q0. The Q2 complement is 1+k and the full state length is 3+k; the coherent Q3 complement is k. Applying PolynomialLocalFiber.exists_rank_fiber_polynomial to the literal Fin 13 to Fin 12 polynomial record gives a nonzero real polynomial D, normalized to one at a witness. O intersect {D nonzero} is nonempty and open, and {D nonzero} is dense in the subtype O.",
                DescribeRole.Theorem,
                "For every point x of that locus and every specified open neighborhood U of x contained in O, the result gives a real subspace K, a continuous linear map q, a C1 parametrization f on a positive-radius ball, and f(0)=x. The dimension of K is positive, and its dimension plus the derivative rank of the polynomial record is thirteen. Every f(z) stays in U and in the certified locus, has exactly the same entire raw Q2 as x, and satisfies q(f(z)-x)=z. For every nonzero z in the ball, the corresponding actual length 3+k states are not related by any complex scalar of norm one. The statement also provides a distinct such point y in U. The phase conclusion uses only the original phase_rigidity and injectivity of the positive representative.",
                "This is a principal generic locus in the canonical parameter domain. Density in the actual MPS state image modulo unit phase requires a separate observable rational inverse and denominator descent and remains open here. The theorem does not resolve full Critch–Morton Conjecture 9 or arbitrary interior windows. It adds no dynamics, time group, energy, physical clock, stability or thermodynamic law, and carries no external open-problem-solution credit. The reused canonical inverse and phase argument retain Haobo Ma and Wenlin Zhang's CC BY 4.0 attribution. The C1 supplier credits BochaoKong's Apache-2.0 LeanPool constant-rank argument at commit 2b1ec889365345f19a45fa94b6457a4d92c96295. Realification, Gram transfer, Schur completion and constant rank are mature mathematics."),
            Paragraph(Text("The interior-genericity consumer also uses evaluate, evaluate_core and evaluate_eta, retaining their exact original proofs. The cross-module consumers use representative_continuous, representative_coordinatesOf, record_equality_density, leadingPolynomial_eval, clear_polynomial, quotientCoordinate_ratio and quotient_denominators_nonzero from this source. Each exposed helper retains its original telescope and proof. Their four-slot audit evidence is unfinished: source-owned typed realization, lawful enrolled readout, complete equivalence, variation, sensitivity, actual observational dependence and accepted source/readout binding are missing. The incomplete audits are disclosed in https://github.com/the-omega-institute/trureturing/issues/30422; public visibility supplies no validated registration.")))));

    private static DocumentBlock Item(string id, string selector, string title, string text,
        DescribeRole role, params string[] continuation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + "." + selector), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks([Paragraph(Text(text)), .. continuation.Select(s => Paragraph(Text(s)))]), role);
}
