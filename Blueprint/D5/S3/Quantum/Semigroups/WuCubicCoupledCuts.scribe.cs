using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuCubicCoupledCutsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuCubicCoupledCuts.";
    private static readonly LibraryNoteRef Wu = LibraryNoteRef.Create("D5/L/SpinModels/wu2026sharp");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two adjacent overlaps share the middle cut weight, with opposite signed parity terms at the ends.",
        H("Coupled occupation cuts in a two-mode CAR frame"),
        Blocks(
            Paragraph(Text("Take any complex orthonormal frame ψ₀, ψ₁, ψ₂, ψ₃. " +
                "The two jumps in occupation order are E₀₁−E₂₃ and E₀₂+E₁₃. " +
                "Write wᵢⱼ for the sum of squared jump amplitudes from ψⱼ to ψᵢ, and sᵢⱼ = wᵢⱼ+wⱼᵢ. " +
                "Dᵢⱼ sums s across pairs crossing both cuts, so D₀₁ = s₀₂+s₀₃, D₁₂ = s₀₃+s₁₃, " +
                "and D₁₁ sums all four edges from the lower pair to the upper pair. " +
                "Let tᵢ be the odd mass, yᵢ = 1−2tᵢ, and zᵢ the empty-minus-full charge of ψᵢ. " +
                "Use the odd offset u = t₀+t₁−1 and v = |z₀+z₁|. " +
                "The Lean even offset is −u. The frame bounds apply also at zero and repeated spectral levels.")),
            Entry("adjacent-cut-weight-eq", "adjacentCutWeight_eq", "Exact shared parity correction",
                "Put fᵢ = tᵢ(1−tᵢ). Then D₀₁ = D₁₁/2+f₁−f₀ and D₁₂ = D₁₁/2+f₂−f₃. " +
                "The diagonal jump weight is fᵢ and the row-plus-column marginal is 2. " +
                "Subtracting the marginals within each pair cancels its internal edge. " +
                "The pair odd masses are 1+u and 1−u, giving f₁−f₀ = −y₀u−u² and f₂−f₃ = y₃u−u²."),
            Entry("absolute-offset-and-imbalance", "abs_cutEvenOffset_add_abs_cutImbalance_le_one",
                "Feasible parity and charge",
                "The empty and full masses a,b of the lower pair lie in [0,1]. " +
                "Since a+b = 1−u and v = |a−b|, the two masses give |u|+v ≤ 1."),
            Entry("adjacent-cut-weight-ge-signed", "adjacentCutWeight_ge_signed", "Signed adjacent bounds",
                "The middle cut satisfies D₁₁ ≥ 1+v²+3u². Substituting this in the exact overlap identities " +
                "gives D₀₁ ≥ (1+v²)/2−y₀u+u²/2 and D₁₂ ≥ (1+v²)/2+y₃u+u²/2."),
            Entry("adjacent-cut-weight-ge-max", "adjacentCutWeight_ge_max", "Local and coupled bounds",
                "At the lower and upper ends take i = 0 and i = 3 respectively. " +
                "Each overlap is at least the maximum of 1−2tᵢ(1−tᵢ) and " +
                "(1+v²)/2−(2qᵢ−1)(1−v), where qᵢ = max(tᵢ,1−tᵢ). " +
                "The first term uses sᵢⱼ ≤ 1 on the internal edge. The second uses |u| ≤ 1−v."),
            Entry("adjacent-cut-weight-ge-quadratic", "adjacentCutWeight_ge_quadratic",
                "Quadratic adjacent bounds",
                "Averaging the signed bound with the local bound (1+yᵢ²)/2 gives " +
                "D₀₁ ≥ 1/2+v²/4+(y₀−u)²/4 and D₁₂ ≥ 1/2+v²/4+(y₃+u)²/4."),
            Entry("end-cut-charge-abs-le", "endCutCharge_abs_le", "End charges on the upper side",
                "The charges of the upper spectral projections are R₀ = −z₀, R₁ = −(z₀+z₁), and R₂ = z₃. " +
                "The two endpoint inequalities are |R₀| ≤ min((1+y₀)/2, v+(1−y₀)/2−u) and " +
                "|R₂| ≤ min((1+y₃)/2, v+(1−y₃)/2+u). Each minimum uses the even mass of the end column " +
                "and the sum of v and the even mass of its partner."),
            Entry("retained-cut-cost-ge-quadratic", "retainedCutCost_ge_quadratic",
                "Weighted relaxation of the physical cuts",
                "For nonnegative Aᵢ, Bᵢ, Z₀, and Z₂, the retained cost is " +
                "∑ᵢ(AᵢDᵢᵢ+BᵢRᵢ)+Z₀D₀₁+Z₂D₁₂, with i from 0 to 2. " +
                "Here D₀₀ = s₀₁+s₀₂+s₀₃ = (3+y₀²)/2 and D₂₂ = s₀₃+s₁₃+s₂₃ = (3+y₃²)/2. " +
                "Put L = Z₀/2, R = Z₂/2, and S = (L+R)/2. The cost is bounded below by " +
                "A₁+(Z₀+Z₂)/2+(3A₀+3A₂−B₀−B₂)/2+(A₁+S)v²−B₁v+(3A₁+S)u² " +
                "−(Ly₀−Ry₃)u+(A₀+L)y₀²/2+(A₂+R)y₃²/2−(B₀y₀+B₂y₃)/2. " +
                "In the signed frame expansion of the equal-cap cubic deficit, Z₀ and Z₂ are the adjacent " +
                "coefficients Z₀₁ and Z₁₂. Dropping the nonnegative long and directed crossings gives this retained cost. " +
                "Adding the thermal and entropy center hT+αQ to the cost bound gives a bound on the normalized deficit."),
            Entry("middle-cut-weight-ge-sqrt-surplus", "middleCutWeight_ge_sqrt_surplus",
                "Surplus from the sharp middle cut",
                "Adding the two directed square-root bounds gives " +
                "D₁₁ ≥ 2+2u²−√((1−(u+v)²)(1−(u−v)²)). " +
                "Set M = 1−u²−v². The excess of this square-root bound over 1+v²+3u² is " +
                "M−√(M²−4u²v²), which is nonnegative. For any 0 ≤ lo < 1 with lo ≤ v, " +
                "multiply this excess by the conjugate sum " +
                "to obtain 4u²v². The conjugate sum is at most 2(1−lo²), giving the additional lower bound " +
                "f(lo)u² with f(lo) = 2lo²/(1−lo²). The multiplication argument includes the endpoint v = 1, " +
                "where u = 0."),
            Entry("adjacent-cut-weight-ge-sqrt-surplus", "adjacentCutWeight_ge_sqrt_surplus",
                "Transfer of the surplus to adjacent overlaps",
                "For 0 ≤ lo < 1 and lo ≤ v, each overlap is bounded below by " +
                "half of 1+v²+(3+f(lo))u² plus its exact diagonal correction f₁−f₀ or f₂−f₃. " +
                "In a weighted mixture using fractions λ₀ and λ₂ of the signed adjacent bounds, " +
                "the middle cut has coefficient H = A₁+(λ₀Z₀+λ₂Z₂)/2. Thus on any closed interval for v " +
                "with lower endpoint lo, the surplus adds f(lo)H to the coefficient of u²."))));

    private static DocumentBlock Entry(string id, string declaration, string title, string claim) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Wu),
            Blocks(Paragraph(Text(claim))), DescribeRole.Theorem);
}
