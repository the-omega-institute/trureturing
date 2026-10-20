using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class GibbsEqualityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equality in finite Gibbs' inequality characterizes identical probability distributions.",
        H("Equality in Gibbs' Inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-relative-entropy-characterizes-equal-distributions"),
                DeclarationHandle.Create("D5/S3/Divergence/GibbsEquality.kl_divergence_eq_zero_iff"),
                H("Zero relative entropy characterizes equal distributions"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, F.Id("I"), Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("I"), Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                                    F.Id("I"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1),
                                    Close, Sp, Land, Sp, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1),
                                    Close, Sp, Land, Sp, RowBreak,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(0),
                                    Sp, Rightarrow, Sp,
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(0), Close,
                                    Sp, Rightarrow, RowBreak,
                                    F.Id("D"), Open,
                                    F.Id("p"), Vert, Sp, F.Id("q"), Close,
                                    Eq, D(0), Sp, Leftrightarrow, Sp,
                                    F.Id("p"), Eq, F.Id("q"), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Let I be a finite alphabet. Let p and q be nonnegative normalized real " +
                                        "mass functions, and assume discrete absolute continuity: q(i) = 0 " +
                                        "implies p(i) = 0. The divergence D is the real-valued finite " +
                                        "klDivergence introduced in ClassicalDPI. Equality p = q is equality of " +
                                        "functions and hence asserts p(i) = q(i) at every letter i.")),
                                    Paragraph(Text(
                                        "Normalization rewrites D(p||q) as the finite sum of " +
                                        "q(i) klFun(p(i)/q(i)). Every summand is nonnegative. If their sum is " +
                                        "zero, the finite nonnegative-sum criterion makes every summand zero. " +
                                        "Where q(i) is positive, Mathlib's unique-zero theorem for klFun gives " +
                                        "p(i)/q(i) = 1 and therefore p(i) = q(i). Where q(i) is zero, absolute " +
                                        "continuity gives the same conclusion directly.")),
                                    Paragraph(Text(
                                        "Conversely, if p and q agree pointwise, every defining summand of the " +
                                        "divergence vanishes. Thus D(p||q) = 0 if and only if p = q. The proof " +
                                        "uses the previously established Gibbs nonnegativity theorem and the " +
                                        "strict zero characterization already supplied by Mathlib; it introduces " +
                                        "neither a new divergence nor a second strict-convexity proof.")),
                                    Paragraph(Text(
                                        "Finite Gibbs variational application. Let Ω be the actual finite nonempty sample or path space, let C : " +
                                        "Ω → ℝ be any real cost, and let R : Ω → ℝ be a strictly positive reference probability: R(ω) > 0 at " +
                                        "every point and ∑ω R(ω) = 1. Fix a temperature τ > 0. The admissible laws are all functions P : Ω → ℝ " +
                                        "with P(ω) ≥ 0 and ∑ω P(ω) = 1; zero coordinates are allowed. All sums below range over the entire Ω and " +
                                        "all logarithms are natural. This finite classical application uses the existing " +
                                        "ClassicalDPI.klDivergence, GrandmotherTheorem.kl_divergence_nonneg and " +
                                        "GibbsEquality.kl_divergence_eq_zero_iff. It requires no full-support hypothesis on P.")),
                                    Paragraph(Text(
                                        "Write E(P) = ∑ω P(ω)C(ω), H(P) = −∑ω P(ω) log P(ω), and Jτ(P) = E(P) + τ D(P||R), with a zero P summand " +
                                        "interpreted as zero. The entropy H is the Shannon sum already defined by " +
                                        "Entropy.MaxEntropy.shannonEntropy via negMulLog. Expanding the logarithm on nonzero P coordinates and " +
                                        "treating zero coordinates separately gives Jτ(P) = E(P) − τ H(P) − τ ∑ω P(ω) log R(ω). The last term is " +
                                        "the reference contribution and generally depends on P. If R is the uniform law 1/|Ω|, normalization " +
                                        "makes this contribution +τ log |Ω|, so Jτ(P) = E(P) − τ H(P) + τ log |Ω|. The exact identity " +
                                        "D(P||uniform) = log |Ω| − H(P) is the local hidentity in the existing MaxEntropy proof; the public " +
                                        "entropy upper bound alone is not that identity.")),
                                    Paragraph(Text(
                                        "Define the actual weighted partition sum Zτ = ∑ω R(ω) exp(−C(ω)/τ), the Gibbs law Qτ(ω) = R(ω) " +
                                        "exp(−C(ω)/τ)/Zτ, and Fτ = −τ log Zτ. Every weighted summand is strictly positive. Nonemptiness supplies " +
                                        "a summand and hence Zτ > 0. Division then gives Qτ(ω) > 0 at every point, while summing the defining " +
                                        "numerator gives ∑ω Qτ(ω) = Zτ/Zτ = 1. Thus Qτ is an admissible law constructed from C, R and τ, rather " +
                                        "than a presumed feasible minimizer.")),
                                    Paragraph(Text(
                                        "For P(ω) > 0, substitute the displayed Qτ into the ratio to obtain log(P(ω)/Qτ(ω)) = log(P(ω)/R(ω)) + " +
                                        "C(ω)/τ + log Zτ. Multiplication by P(ω) makes the same equality valid when P(ω) = 0 under the " +
                                        "zero-summand convention. Summing and using ∑ω P(ω) = 1 gives D(P||Qτ) = D(P||R) + E(P)/τ + log Zτ. " +
                                        "Rearrangement is the exact Gibbs decomposition Jτ(P) = Fτ + τ D(P||Qτ), including every admissible P " +
                                        "with zero coordinates and the general nonuniform R.")),
                                    Paragraph(Text(
                                        "In the nonnegativity and equality declarations use the explicit parameter correspondence I = Ω, p = P " +
                                        "and q = Qτ. The probability premises follow from admissibility of P and the normalization just proved " +
                                        "for Qτ. Absolute continuity follows from strict positivity of Qτ: it has no zero coordinate. " +
                                        "Nonnegativity therefore gives Jτ(P) ≥ Fτ. Since τ > 0, equality holds exactly when D(P||Qτ) = 0, and the " +
                                        "equality theorem makes this equivalent to P = Qτ as functions on the whole Ω. Applying the result to the " +
                                        "proved admissible Qτ gives Jτ(Qτ) = Fτ. Hence Fτ is the attained global minimum over all probability " +
                                        "laws, with Qτ its unique minimizer; neither minimization nor attainment is an input assumption.")),
                                    Paragraph(Text(
                                        "For the zero-temperature statement, define c* to be the minimum of the actual nonempty finite image " +
                                        "{C(ω) : ω ∈ Ω}. Finset.min'_mem supplies a point attaining c*, and Finset.min'_le gives c* ≤ C(ω) at " +
                                        "every point. Let G* = {ω ∈ Ω : C(ω) = c*} be the entire ground set and put r* = ∑ω∈G* R(ω), equivalently " +
                                        "∑ω (if C(ω) = c* then R(ω) else 0). All its summands are nonnegative, and the attained ground point " +
                                        "contributes a strictly positive R value, so r* > 0. The quantity r* includes every minimizer, including " +
                                        "ties; it is not a chosen single-point mass or an assumed lower bound.")),
                                    Paragraph(Text(
                                        "For each τ > 0, the ground contribution to Zτ is exactly r* exp(−c*/τ), and every remaining summand is " +
                                        "nonnegative. This proves r* exp(−c*/τ) ≤ Zτ. Conversely, c* ≤ C(ω), positive division by τ and " +
                                        "monotonicity of exp imply exp(−C(ω)/τ) ≤ exp(−c*/τ). Multiply by R(ω) ≥ 0, sum over all Ω and use ∑ω " +
                                        "R(ω) = 1 to get Zτ ≤ exp(−c*/τ). These are the two partition bounds for arbitrary real costs, without " +
                                        "any sign restriction on C.")),
                                    Paragraph(Text(
                                        "Taking logarithms on the positive quantities in this sandwich and multiplying by −τ reverses the " +
                                        "inequalities, giving both free-energy bounds c* ≤ Fτ ≤ c* − τ log r*. Here r* is fixed once C and R are " +
                                        "fixed and is strictly positive, so log r* is a finite real number. As τ tends to zero through positive " +
                                        "values, the lower constant c* and upper expression c* − τ log r* both tend to c*. The squeeze theorem " +
                                        "therefore yields Fτ → c* along exactly nhdsWithin 0 (Ioi 0), the right-hand positive-temperature filter. " +
                                        "No value or Gibbs law at τ = 0 is required, and this free-energy limit does not assert convergence of a " +
                                        "minimizing law.")),
                                    Paragraph(Text(
                                        "When Ω is a path set, c* is its minimum cost; it describes geometric shortest paths only when C " +
                                        "is the corresponding geometric length. The hypotheses are finite nonempty Ω, arbitrary real C, " +
                                        "strictly positive normalized R and positive " +
                                        "temperature; P ranges over the full nonnegative normalized simplex. No continuum approximation, " +
                                        "infinite-space integrability claim, physical realization, efficiency claim or literature-novelty claim " +
                                        "follows from this finite result. The weighted Gibbs formulas, the minimum and the entire ground mass " +
                                        "above are the application objects; the substantive inference reuses the existing KL nonnegativity, its " +
                                        "zero characterization, the source-local uniform identity, finite-sum order and real " +
                                        "logarithm/exponential/limit APIs."))),
                DescribeRole.Theorem
            ))));
}
