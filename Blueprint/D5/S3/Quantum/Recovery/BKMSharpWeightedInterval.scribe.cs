using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMSharpWeightedIntervalDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMSharpWeightedInterval.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp weighted bounds and equality defects for qutrit BKM step profiles.",
        H("Sharp weighted interval estimates for BKM step profiles"),
        Blocks(
            Entry("interval-weight", "intervalWeight", "Interval mass",
                "The mass assigned to endpoints a and b is the difference of their inverses.", DescribeRole.Definition),
            Entry("interval-coefficient", "intervalCoefficient", "Interval coefficient",
                "The coefficient ab(b−a) extends continuously to equal endpoints and to a zero left endpoint.", DescribeRole.Definition),
            Entry("interval-weight-integral", "intervalWeight_eq_integral", "Weighted interval mass",
                "For 0 < a ≤ b this mass is the integral of dx/x² from a to b.", DescribeRole.Theorem),
            Entry("step-integral", "stepIntegral", "Integral of one level",
                "Scale the constant vector by the length of the interval.", DescribeRole.Definition),
            Entry("step-energy", "stepEnergy", "Energy of one level",
                "Multiply the squared norm of the level by the weighted interval mass.", DescribeRole.Definition),
            Entry("step-integrals", "step_integrals", "Integral formulas for one level",
                "For 0 < a ≤ b and a real normed vector space E with CompleteSpace E, stepIntegral agrees with the vector integral against dx "
                + "and stepEnergy agrees with the integral of the squared norm against dx/x², both from a to b.", DescribeRole.Theorem),
            Entry("mesh-coefficient", "meshCoefficient", "Three-interval coefficient",
                "Add the coefficients of the last two intervals of the mesh 0, x, x+y, x+y+z. The level on the first interval is zero.", DescribeRole.Definition),
            Entry("mesh-cubic-form", "meshCoefficient_eq_cubes", "Cubic form of the coefficient",
                "The sum of the interval coefficients is one third of the difference between the cube of the total length and the sum of the cubes of the three lengths.", DescribeRole.Theorem),
            Entry("mesh-deficit", "three_interval_mesh_deficit", "Exact spacing deficit",
                "For mean length m, the difference from 8/27 times the cube of the total length is the sum of (x−m)²(x+2m), (y−m)²(y+2m), and (z−m)²(z+2m), divided by three.", DescribeRole.Theorem),
            Entry("mesh-sharp", "three_interval_mesh_sharp", "Optimal spacing",
                "For nonnegative lengths and positive total length the coefficient is at most 8/27 times the cube of the total length, with equality exactly at equal spacing.", DescribeRole.Theorem),
            Entry("mesh-integral", "meshIntegral", "Mesh integral",
                "Add the integrals of the two active levels.", DescribeRole.Definition),
            Entry("mesh-energy", "meshEnergy", "Mesh energy",
                "Add the weighted energies of the two active levels.", DescribeRole.Definition),
            Entry("energy-deficit", "three_interval_energy_deficit", "Exact level deficit",
                "For positive lengths set p=x(x+y) and q=(x+y)(x+y+z). The mesh coefficient times the energy minus the squared integral is yz/(pq) times the squared norm of q·u−p·w.", DescribeRole.Theorem),
            Entry("normalized", "three_interval_normalized", "Sharp normalized profile bound",
                "For strictly positive lengths x, y, z with x+y+z=1 and levels u, w in a real inner-product space, "
                + "the squared integral is at most 8/27 times the energy. At positive energy equality holds exactly at equal thirds with w=3u.", DescribeRole.Theorem),
            Entry("head-coefficient", "headCoefficient", "Coefficient of the first two jumps",
                "Take the larger of the coefficients for endpoints (s,c) and (t,c).", DescribeRole.Definition),
            Entry("tail-coefficient", "tailCoefficient", "Coefficient of the remaining levels",
                "Add the coefficients for endpoints (c,min(d,T)) and (d,max(d,T)).", DescribeRole.Definition),
            Entry("band-coefficient", "bandCoefficient", "Common coefficient of a band",
                "Add the head and tail coefficients using d=s+t and the common upper cutoff T.", DescribeRole.Definition),
            Entry("tail-identity", "band_tail_identity", "Tail at the unshifted cutoff",
                "At the unshifted cutoff c₀=d−v with T=1−v, the tail coefficient is d(1−d)(1−2v) if d ≤ T and c₀T(1−d) if T < d.", DescribeRole.Theorem),
            Entry("band-coefficient-bound", "band_coefficient_bound", "Uniform band coefficient",
                "Set d=s+t, c=d−v−η, and T=1−v. If 0 < s ≤ t < c, d ≤ 1, v ≥ 0, and η ≥ 0, "
                + "the band coefficient is bounded by the three-interval coefficient for lengths s, t, and 1−d, plus η. "
                + "Equivalently, the bound is 8/27+η minus the exact spacing deficit for those lengths.", DescribeRole.Theorem),
            Entry("jump-correction", "jumpCorrection", "Correction for the two jumps",
                "The correction matches the mixed terms of the two head quadratic forms after the energy is multiplied by the head coefficient.", DescribeRole.Definition),
            Entry("jump-correction-gap", "jumpCorrection_eq_gap", "Correction from the threshold gap",
                "For 0 < s ≤ t < c ≤ s+t the correction is 2(c−t)(t−s)/(stc), positive exactly when s<t.", DescribeRole.Theorem),
            Entry("head-integral", "headIntegral", "Head integral",
                "The levels on the first two active intervals are the first jump and the sum of both jumps.", DescribeRole.Definition),
            Entry("head-energy", "headEnergy", "Head energy",
                "Weight the squared norms of the first jump and of the sum of both jumps by the masses of their intervals.", DescribeRole.Definition),
            Entry("row-integral", "rowIntegral", "Integral with a row cutoff",
                "Add the head integral and the two tail integrals, allowing a collapsed interval when the row ends before s+t.", DescribeRole.Definition),
            Entry("row-energy", "rowEnergy", "Energy with a row cutoff",
                "Add the head energy and the two tail energies truncated at the row cutoff.", DescribeRole.Definition),
            Entry("band-row", "band_row_bound", "Signed row bound",
                "For levels in a real inner-product space, assume 0 < s ≤ t < c ≤ d=s+t and c ≤ r ≤ T. "
                + "The tail intervals are [c, min(d,r)] and [d, max(d,r)], so the final interval collapses when r ≤ d. "
                + "Weighted Cauchy–Schwarz bounds the squared row integral by the band coefficient C times the row energy plus Cκ⟨a,b⟩, "
                + "where κ is the jump correction and a, b are the first two jumps.", DescribeRole.Theorem),
            Entry("band-sum", "band_row_sum_sharp", "Summing over a band",
                "Set d=s+t, c=d−v−η, and T=1−v. Assume 0 < s ≤ t < c, d ≤ 1, v ≥ 0, and η ≥ 0, with c ≤ r ≤ T for every row in the finite sum. "
                + "The sum of squared row integrals is bounded by (8/27+η) times the total row energy plus Cκ times the signed sum of real inner products of the first two jumps. "
                + "For complex rows these inner products are the real parts of the complex pairings.", DescribeRole.Theorem),
            Entry("saturation", "band_equal_thirds_attains", "Positive-energy saturation",
                "In a real inner-product space, take any jumps a, b with P=a+b≠0. Set s=t=1/3, v=η=0, c=d=2/3, and r=T=1, "
                + "with first tail level u=0 and final level w=3P. The first tail interval collapses and the mixed correction vanishes. "
                + "The row energy is 6‖P‖² and the squared row integral is (16/9)‖P‖², giving equality at 8/27 times the energy.", DescribeRole.Theorem),
            Paragraph(Text(
                "For a faithful joint state τ with retained qutrit marginal ω, the physical energy loss G is the difference of the BKM power-integral pairings at ω and τ for K and its tensor lift. The numerator M is the squared Hilbert–Schmidt norm of the weighted commutator of the lifted K with log τ minus the lifted log ω. With L=log cond(τ) and LG/2=1, the physical reduction must identify the normalized row energies summing to one and give M/(L³G) as half the summed squared row integrals up to a vanishing error.")),
            Paragraph(Text(
                "To apply the band bound, the energy-normalized resolvent rows must converge to the indicated step profiles with the first two jumps recovered from the adjacent retained transitions. The approximation must give a uniform error per unit row energy, allowing growing environment dimension. For a source band starting at v, c=s+t−v−ε−δ and T=1−v. With P the band source projection and U the destination projection onto joint log exponents at most s+t−ε, the required signed sum is the real part of the Hilbert–Schmidt pairing of (I−U)AP√τ and (I−U)BP√τ. Its asymptotic vanishing on the whole band, including rows ending before s+t, is a separate spectral estimate. The scalar factor 8/27 contributes 4/27 after the physical normalization.")))));

    private static DocumentBlock Entry(string id, string name, string title, string prose,
        DescribeRole role) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
