using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicAngularCertificateDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicAngularCertificate.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Matched and refined angular bounds for the physical ordinary-trace cubic deficit.",
        H("Angular certificates for the two-mode Wu cubic deficit"),
        Blocks(
            Paragraph(Text("For the equal-cap, exponent-three specialization of Wu v1, Remark 3.15, " +
                "equation (3.54), use the signed CAR jumps E₀₁−E₂₃ and E₀₂+E₁₃, r = exp(β/3), " +
                "and an embedded spectrum (m,n,q,1) with 0 ≤ m ≤ n ≤ q ≤ 1. " +
                "The unitary U supplies an arbitrary complex orthonormal frame in occupation order. " +
                "Let a = 2t₀, b = 2t₃, S = a+b and F = a−b, where tᵢ is the odd occupation of the i-th frame line. " +
                "Let v be the absolute charge of the lower pair, u its odd offset, and w = 1−v. " +
                "The Lean even offset is −u. Write D₀₂ for the symmetric crossing between the two extreme lines.")),
            Entry("long-crossing-product", "long_crossing_mul", "Product bound for the extreme crossing",
                "The two extreme lines satisfy F²/4 ≤ S D₀₂. The complex determinant estimate uses " +
                "P = √((1−t₀)t₃) and Q = √(t₀(1−t₃)) with D₀₂ ≥ (P−Q)², " +
                "(P+Q)² ≤ 2(t₀+t₃), and P²−Q² = t₃−t₀."),
            Entry("long-crossing-bound", "long_crossing_ge", "Angular long-crossing weight",
                "Define f(S) = max(1,1/S) for S ≠ 0 and f(0) = 0. " +
                "The estimate D₀₂ ≥ f(S)F²/4 follows from the product bound and (P+Q)² ≤ 1. " +
                "It is equation (1) of the lower Gibbs complement proof, with the zero-tilt case included. " +
                "In particular no division by S is needed in the product form."),
            Paragraph(Text("Use nonnegative diagonal cut weights Aᵢ and bias weights Bᵢ, two adjacent coefficients Z₀ = Z₀₁ " +
                "and Z₂ = Z₁₂, and long coefficient Zlong = Z₀₂. The retained cost includes the diagonal cuts, " +
                "signed upper-projection charges, adjacent crossings and Zlong D₀₂. Its occupation reference is " +
                "2∑ Aᵢ−∑ Bᵢ+Z₀+Z₂. Put L₀ = B₁/2−A₁, κ = Zlong/4, " +
                "Pᵢ = (Aᵢ+Zᵢ−L₀)/2 and Gᵢ = Bᵢ/2−2Pᵢ for i = 0,2. " +
                "Write C = P₀a²+P₂b²+G₀a+G₂b for the matched singleton correction.")),
            Entry("matched-cut-bound", "matched_cut_bound", "Matched angular estimate for the cuts",
                "If 0 ≤ L₀ ≤ min(Z₀,Z₂) and Zlong ≥ 0, the same absolute adjacent weight L₀ is used on both sides. " +
                "The middle quadratic coefficient is then A₁+L₀ = B₁/2. The w terms reduce to B₁w²/2 " +
                "and the u terms to (3A₁+L₀)u²+L₀Fu. Completing the u square gives the retained cost lower bound " +
                "occupation cost + C + (κ f(S)−L₀/4)F²."),
            Entry("refined-charge-admissible", "refined_charge_admissible", "Common endpoint charge",
                "Let L be a nonnegative common adjacent weight, ℓ = L−L₀ and H = A₁+L with A₁ ≥ 0. " +
                "If HS/2 ≤ ℓ ≤ min(B₀,B₂), then μ = ℓ−HS/2 lies in [0,min(B₀,B₂)]. " +
                "The same multiplier can therefore be used in both singleton charge inequalities of the physical frame."),
            Entry("refined-cut-bound", "refined_cut_bound", "Refined angular estimate for the cuts",
                "Take L = min(Z₀,Z₂), under the matched mixture conditions, nonnegative Aᵢ, B₁ and Zlong, " +
                "and the common charge admissibility condition. After the common charge is inserted the w terms are " +
                "Hw²−HS w and the linear singleton terms gain HS²/2. The change of singleton weights contributes " +
                "−ℓ(S²+F²)/4 after the linear cancellation. Completing the w square leaves " +
                "(H−ℓ)S²/4 = B₁S²/8. Completing the u square loses L²F²/[4(3A₁+L)]. " +
                "The retained cost is at least occupation cost + C + B₁S²/8 + " +
                "(κ f(S)−ℓ/4−L²/[4(3A₁+L)])F². The middle-square loss is zero when L = 0."),
            Entry("ordinary-trace-identity", "normalized_deficit_eq_ordinary_trace", "Ordinary-trace operator identity",
                "Relabel the unitary U by the two-mode occupation pairs to obtain V, and set " +
                "M = V diag(m,n,q,1) V* and X = G(r)⁻¹ M G(r)⁻¹ using the operator bridge Gibbs factor G. " +
                "For r ≥ 1 the normalized spectral source deficit δ is exactly " +
                "(9/8) Re tr(M² G(r) generator(r,X) G(r)) − α(r) " +
                "(Re tr(M³(log(M³)−log D(r))) − Re tr(M³) log(Re tr(M³))). " +
                "The logarithms are the spectral functional calculus and tr is ordinary trace. " +
                "The identity identifies the left-hand deficit of the angular estimates with the source energy minus entropy " +
                "in the cubic specialization of Wu v1 (3.54)."),
            Entry("signed-cut-identity", "normalized_deficit_eq_cuts", "Exact signed spectral cut expansion",
                "For r ≥ 1 and nonnegative levels the physical deficit equals the thermal and entropy center plus the retained " +
                "cost and the three directed corrections. The diagonal coefficients are cutEnergy and cutBias, the " +
                "adjacent coefficients are lowerCoeff and upperCoeff, and the long coefficient is longCoeff with the " +
                "extra middle gap q−n. The directed terms are proportional to w₂₀+w₃₀, w₃₀+w₃₁ and w₃₀, where " +
                "wᵢⱼ is the sum of squared jump amplitudes from column j to i. For ordered levels these corrections are nonnegative."),
            Entry("occupation-identity", "occupation_deficit_eq", "Occupation deficit identity",
                "At U = 1 the directed corrections and the long crossing vanish, and the physical deficit of the same spectrum " +
                "equals δocc, the thermal and entropy center plus the occupation cut cost. This reference retains the same spectrum " +
                "and the same ordinary-trace normalization."),
            Entry("matched-physical-deficit", "matched_deficit_bound", "Matched inequality for the physical deficit",
                "For r ≥ 1, ordered nonnegative levels bounded by one, and 0 ≤ L₀ ≤ min(Z₀,Z₂) for the physical cut coefficients, " +
                "δ ≥ δocc + C + (κ f(S)−L₀/4)F². This is equation (2) of the lower Gibbs complement proof. " +
                "The exact signed cut identity permits dropping the nonnegative directed terms."),
            Entry("refined-physical-deficit", "refined_deficit_bound", "Refined inequality and the common tilt gain",
                "With the same physical cut coefficients and the further condition HS/2 ≤ ℓ ≤ min(B₀,B₂), equation (3) is " +
                "δ ≥ δocc + C + B₁S²/8 + (κ f(S)−ℓ/4−L²/[4(3A₁+L)])F². " +
                "The extra B₁S²/8 belongs to the actual deficit from the ordinary-trace operator identity. " +
                "In the closed lower Gibbs region proof (research source wu-cubic-lower-gibbs-complement/proof.txt, equations (2)–(3)), " +
                "the range is 26/25 ≤ r ≤ 7/5 with m ≤ r⁻². Near g = (r⁻²,r⁻¹,r⁻¹,1), let d = maxᵢ |xᵢ−gᵢ|. " +
                "For 0 < d ≤ 1/256 and 1049/1000 ≤ r ≤ 7/5, the proof uses (2) for S ≥ dK and (3) for S ≤ dK. " +
                "It checks P₀,P₂ > 0 and κ ≥ L₀/4, chooses K from G₀/d, G₂/d and the Pᵢ, " +
                "and verifies HdK/2 ≤ ℓ ≤ min(B₀,B₂) on the small-tilt branch. " +
                "The extra gain changes the coefficient of S² in the small-tilt quadratic to (P₀+P₂+B₁/2)/4. " +
                "This is the quadratic used by the lower Gibbs proof before its Gibbs-relative minimization and exact interval replay. " +
                "The Lean theorem supplies the physical frame inequality conditional on those coefficient and charge comparisons. " +
                "The full temperature and spectral cover is established in the cited research proof by separate exact replays."),
            Entry("repeated-middle-reduction", "repeated_middle_angular_bound", "Repeated middle level",
                "When q = n and 0 ≤ m ≤ n ≤ 1, A₁, B₁, Z₀, Z₂, L₀, L and μ vanish. " +
                "Both mixture and charge conditions hold in every complex frame for r ≥ 1. The refined gain and mixture losses vanish, " +
                "leaving δ ≥ δocc + singletonCorrection(U,A,B,0,0,0) + κ f(S)F². " +
                "The nonzero end gaps can still contribute through the long crossing, so this reduction includes the zero middle gap " +
                "without division by that gap."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
