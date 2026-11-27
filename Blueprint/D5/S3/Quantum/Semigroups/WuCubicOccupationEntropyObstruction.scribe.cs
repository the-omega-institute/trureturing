using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicOccupationEntropyObstructionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicOccupationEntropyObstruction.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A faithful two-mode CAR product family violates the proposed cubic entropy bound by 4Q*.",
        H("Finite-amplitude obstruction at matched occupation"),
        Blocks(
            Entry("entropy-slope", "entropySlope_mul_le_fixedOccupationEntropy", "Fixed-diagonal entropy slope",
                "For real a < b with a+b = 1 and 0 ≤ z < ab, put d = √((b−a)²+4z), " +
                "λ± = (1±d)/2, and F(a,b,z) = ∑± λ± log λ± − a log a − b log b. " +
                "Then F(a,b,z) ≥ z ψ(a,b), where ψ(a,b) = (log b − log a)/(b−a). " +
                "Convexity of log(1+d) − log(1−d) makes its ratio to d nondecreasing, " +
                "so the entropy derivative is bounded below by its value at z = 0."),
            Entry("finite-amplitude-obstruction", "finite_amplitude_obstruction", "Scalar margin",
                "Assume 0 < a < b, a+b = 1, η > 0 and 0 < z ≤ abη/(2+η). With " +
                "s = √(ab), r = √(ab−z), and α ψ(a,b) = 2(1+η)/(1+2s), the bound is " +
                "0 < ηz/(1+2s) ≤ α F(a,b,z) − 4s(s−r−z/(1+2r)). " +
                "The amplitude bound controls the quadratic defect uniformly over this interval."),
            Paragraph(Text("For a positive Gibbs half-gap h, put a = exp(−h)/(2 cosh h), " +
                "b = exp(h)/(2 cosh h), c = cosh(h/3), η = (c−1)(c+2)/[2(2c+1)²], and " +
                "zmax = abη/(2+η). Write α₃ = (9/2) sinh(h/3) sinh(2h/3)/(2h sinh h), " +
                "the cubic coefficient in Wu v1, Remark 3.15, (3.55).")),
            Entry("matched-product-obstruction", "matched_product_obstruction", "Faithful CAR product states",
                "Let w be complex with 0 < z = |w|² ≤ zmax. Put d = diag(a,b), let σ have diagonal " +
                "(a,b) and off-diagonal entries w and its conjugate, and set ρ = d ⊗ σ and D = d ⊗ d. " +
                "The matrices d, σ and ρ are positive definite with ordinary trace one. For each of the " +
                "two signed CAR lowering jumps Jₖ, Aₖ = Re Tr(ρ JₖJₖ†) = a and " +
                "Bₖ = Re Tr(ρ Jₖ†Jₖ) = b. With Tₖ = Re Tr(√ρ Jₖ √ρ Jₖ†), " +
                "Q* = ∑ₖ √(AₖBₖ)(√(AₖBₖ) − Tₖ), and S = Re Tr(ρ(log ρ − log D)), the theorem gives " +
                "0 < ηz/(1+2√(ab)) ≤ α₃ S − 4Q*. The Gibbs factor makes the first quadratic " +
                "defect zero. The second overlap is r + z/(1+2r), and S = F(a,b,z). " +
                "The strict gap concerns the proposed bound α₃ S ≤ 4Q* for the entropy term in (3.54)."),
            Entry("amplitude-interval", "amplitude_interval", "An interval of distinct witnesses",
                "For each h > 0, zmax is positive. The map z ↦ ρ with w = √z is injective on " +
                "0 < z ≤ zmax. Every z in that interval is realized by a complex w with |w|² = z " +
                "whose product state is positive definite of trace one and satisfies 4Q* < α₃ S."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
