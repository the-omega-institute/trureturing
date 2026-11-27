using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicTranslationEnergyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicTranslationEnergy.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    private static DocumentBlock.Describe Result(string id, string declaration, string title, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact charge-weighted slope and centered degree gap for the Wu cubic translation energy.",
        H("Scalar translations of the Wu cubic energy"),
        Blocks(
            Paragraph(Text("Take r ≥ 1 unless otherwise specified. Write B = G² and U(X) = GXG, with G⁶ = D the two-mode Gibbs density. The cubic energy is (9/8) Re Tr(U(X)² U(LX)), where L is the signed generator. The variance V(A) is Re Tr(B U(A)²).")),
            new DocumentBlock.Section(H("Stationarity and the trace slope"), Blocks(
                Result("stationarity", "stationary", "Gibbs stationarity",
                    "For every complex direction A, Tr(D L(A)) = 0. Pairing with the identity extracts the degree-zero coordinate, which the generator annihilates."),
                Result("affine-translation", "cubicEnergy_translate", "Affine energy along scalar translations",
                    "For any complex A and real t, L(A + tI) = L(A) and U(A + tI) = U(A) + tB. The quadratic coefficient vanishes by cyclicity of trace and stationarity. The energy at A + tI is the energy at A plus t times (9/8) Re Tr((B U(A) + U(A) B) U(L(A)))."),
                Result("trace-derivative", "cubicEnergy_hasDerivAt_trace", "Derivative in trace form",
                    "For every complex A, the trace coefficient of the affine formula is the derivative at every real t."))),
            new DocumentBlock.Section(H("Variance on signed charge blocks"), Blocks(
                Result("charge-multiplier", "entryMultiplier_of_direction", "Entry multiplier on the support of a direction",
                    "Write bᵢ for the ith diagonal entry of B. At each nonzero entry (i,j) of a basis direction of signed charge q, the modular eigenrelation gives bᵢ/bⱼ = r^q. The ratio of the ordinary variance weight to the Gibbs pairing weight is therefore m(q) = (r^q + 1)/(2√(r^q))."),
                Result("variance-pairing", "vPairing_expansion", "Diagonal ordinary-trace variance pairing",
                    "For arbitrary complex X and Y, the pairing is half the trace of (B U(X)ᴴ + U(X)ᴴ B) U(Y). The charge multiplier rescales each Gibbs-orthogonal direction, so the pairing is the sum of the conjugate X-coordinate times the Y-coordinate times m(q) and the squared Gibbs norm of that direction."),
                Result("variance-entries", "V_eq_entries", "Entry formula for Hermitian directions",
                    "For every real r and Hermitian A, V(A) is the sum of |Aᵢⱼ|² weighted by bᵢ bⱼ (bᵢ + bⱼ)/2. Hermiticity identifies the real part of the pairing of A with itself with the original trace variance."),
                Result("component-mass", "vWeight_eq_component", "Variance weight of a single complex component",
                    "For any complex A and basis label k, let Z be the kth coordinate of A times its basis direction. The variance weight wₖ is the squared modulus of that coordinate times the charge-rescaled squared Gibbs norm. It equals the same entry-weighted sum of |Zᵢⱼ|², including when Z is non-Hermitian."),
                Result("variance-mass", "V_eq_sum", "Variance as a sum of component weights",
                    "For Hermitian A, V(A) is the sum of the sixteen nonnegative weights wₖ."))),
            new DocumentBlock.Section(H("Degree-weighted slope and centered gap"), Blocks(
                Result("degree-derivative", "cubicEnergy_hasDerivAt_degree", "Exact charge-weighted derivative",
                    "For Hermitian A and every real t, the derivative of the cubic energy at A + tI along the translation is (9/4) times the sum of dₖ wₖ. Here dₖ is the generator degree of the kth signed thermal direction."),
                Result("degree-gap", "degree_sum_ge", "Degree gap for the centered variance",
                    "If A is Hermitian and Tr(DA) = 0, the identity coordinate vanishes. The degree-one mass V₁ contributes once and all other surviving weights contribute at least twice. The sum of dₖ wₖ is at least 2V − V₁."),
                Result("derivative-lower-bound", "cubicEnergy_deriv_ge", "Lower bound for the translation derivative",
                    "For every Gibbs-centered Hermitian A and real t, the derivative at t is at least (9/4)(2V − V₁)."))))));
}
