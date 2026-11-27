using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class ActualCanonicalLiForwardPairedResolventDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Probability/ActualCanonicalLiForwardPairedResolvent";

    private static DocumentBlock Entry(string id, string name, string title, string statement, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Under right-half-plane nonvanishing, the actual square resolvent gives the "
        + "derivative-normalized Li coefficients as a sum over zero pairs.",
        H("Canonical Li coefficients from actual zero pairs"),
        Blocks(
            Entry("actual-zero-ratio", "zeroRatio", "Cayley ratio of an actual zero",
                "For each natural index i, the ratio is 1 - 1/rho_i, where rho_i is the corresponding "
                + "nontrivial zeta zero in zetaZeroData.", DescribeRole.Definition),
            Entry("pair-coefficient", "pairCoefficient", "Contribution from a positive-ordinate zero",
                "For natural n and i, the value at a positive ordinate is twice the analytic multiplicity "
                + "times (1 minus the real part of the nth power of the Cayley ratio). It is zero at other "
                + "indices. On the critical line this is the multiplicity times the squared norm of one "
                + "minus that power. The unit norm of the Cayley ratio gives the bound by n squared "
                + "times the first contribution through the geometric telescoping identity.", DescribeRole.Definition),
            Entry("pair-summability", "pairCoefficient_abs_summable", "Convergence of the actual pair series",
                "For every natural n, the absolute values of the real pair contributions are summable over all natural indices. "
                + "Restriction of the summable real Li summand to positive ordinates and multiplication "
                + "by two give the series.", DescribeRole.Theorem),
            Entry("pair-sum", "pairSum", "Actual pair sum",
                "For every natural n, the pair sum is the sum of the summable pair contributions "
                + "in degree n.", DescribeRole.Definition),
            Entry("canonical-pair-equality", "canonicalLiCoefficient_eq_actual_pairSum",
                "Derivative-normalized coefficient identity",
                "For every natural n, if n is zero or the completed xi function is nonzero on the "
                + "open right half-plane with real part greater than one half, the derivative-normalized "
                + "canonical Li coefficient is exactly the actual pair sum. At index zero both sides "
                + "vanish. Right-half-plane nonvanishing and the functional equation place all zeros on "
                + "the critical line. The positive-ordinate square resolvent "
                + "gives the sum of the conjugate pairs of simple fractions for the logarithmic derivative. "
                + "The Mobius change of variable yields three geometric series per pair. The first pair "
                + "contribution times polynomially weighted geometric decay dominates the series in both "
                + "indices on the unit disk. Exchanging these sums and using uniqueness of scalar power "
                + "series identifies the canonical coefficient.", DescribeRole.Theorem),
            Entry("fixed-quadratic-forward", "canonical_li_forward_fixed_quadratic",
                "Fixed first-coefficient quadratic bound",
                "For each natural n, under the same alternative of index zero or right-half-plane "
                + "nonvanishing, the canonical coefficient lies in the closed interval from zero to "
                + "the actual first canonical coefficient times n squared. This follows by summing "
                + "the pointwise squared-norm bounds and using the coefficient identity at n and at one.",
                DescribeRole.Theorem),
            Entry("nonnegative-criterion", "rh_iff_canonical_li_nonnegative", "Canonical Li nonnegativity criterion",
                "The standard Riemann hypothesis holds exactly when the canonical Li coefficient is "
                + "nonnegative at every natural index. The reverse direction uses the positive-index "
                + "canonical Li criterion.", DescribeRole.Theorem),
            Entry("fixed-quadratic-criterion", "rh_iff_canonical_li_fixed_quadratic",
                "Canonical Li criterion with fixed quadratic bound",
                "The standard Riemann hypothesis holds exactly when for every natural n the canonical "
                + "Li coefficient lies between zero and the first coefficient times n squared, inclusive. "
                + "The reverse direction uses the canonical quadratic growth criterion.", DescribeRole.Theorem))));
}
