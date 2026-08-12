using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class EntropyNonnegDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Shannon and conditional entropy are nonnegative in nats, completing the finite Shannon-entropy bracket.",
        H("Nonnegativity of Finite Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-shannon-entropy-is-nonnegative"),
                DeclarationHandle.Create("D5/S3/Entropy/EntropyNonneg.shannon_entropy_nonneg"),
                H("Finite Shannon entropy is nonnegative"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("i")),
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1),
                                    Close, Sp, Rightarrow, RowBreak,
                                    D(0), Le, Sp,
                                    Operatorname, Grp(F.Id("shannonEntropy")),
                                    Open, F.Id("p"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "This result supplies the lower bound that the entropy bucket was " +
                                        "missing. The sibling maximum-entropy theorem already proves H <= log " +
                                        "card on a finite nonempty alphabet, but without this theorem nothing " +
                                        "ruled out negative entropy for a legitimate distribution. Together, " +
                                        "the two bounds place its Shannon entropy in [0, log card].")),
                                    Paragraph(Text(
                                        "Each summand is Mathlib's Real.negMulLog, which is nonnegative on the " +
                                        "unit interval. The proof applies Real.negMulLog_nonneg term by term " +
                                        "and sums the resulting inequalities; it follows the library-before-" +
                                        "proof principle rather than re-deriving the scalar lemma. The upper " +
                                        "endpoint p(i) <= 1 is derived, not assumed: nonnegativity gives " +
                                        "p(i) <= sum_j p(j), and normalization identifies that sum with 1.")),
                                    Paragraph(Text(
                                        "Normalization is genuinely required for this lower bound. Without a " +
                                        "unit sum, a single mass of 2 has Real.negMulLog 2 < 0, so the entropy " +
                                        "can be negative. This differs from several sibling identities in this " +
                                        "bucket, which need only nonnegativity; the unit-sum hypothesis here is " +
                                        "therefore substantive rather than gratuitous. The units are nats " +
                                        "because Real.negMulLog uses the natural logarithm.")),
                                    Paragraph(Text(
                                        "No equality condition is claimed. In particular, this theorem does " +
                                        "not prove that entropy vanishes exactly on point masses, and it says " +
                                        "nothing about strict positivity for non-degenerate distributions."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("finite-conditional-entropy-is-nonnegative"),
                DeclarationHandle.Create("D5/S3/Entropy/EntropyNonneg.conditional_entropy_nonneg"),
                H("Finite conditional entropy is nonnegative"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Colon, Sp,
                                    Iota, Times, Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("p"), Open,
                                    F.Id("i"), Comma, F.Id("j"), Close,
                                    Close, Sp, Rightarrow, RowBreak,
                                    D(0), Le, Sp,
                                    Operatorname, Grp(F.Id("conditionalEntropy")),
                                    Open, F.Id("p"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Conditional entropy is a sum of marginal weights times the Shannon " +
                                        "entropies of conditional slices. For every nonzero marginal, the " +
                                        "corresponding quotient slice is nonnegative and has unit sum, so the " +
                                        "preceding Shannon bound applies. This normalization is derived from " +
                                        "the marginal definition; no global unit-sum hypothesis is imposed on " +
                                        "the joint. The outer marginal weights are nonnegative because they are " +
                                        "finite sums of nonnegative joint masses.")),
                                    Paragraph(Text(
                                        "A zero marginal is the essential exceptional case. Its conditional " +
                                        "slice is defined by quotienting by zero and is not a distribution, so " +
                                        "the per-slice Shannon bound does not apply. The proof handles this by " +
                                        "cases: the outer weight is zero, and its entire conditional-entropy " +
                                        "term vanishes. No positivity is assumed anywhere.")),
                                    Paragraph(Text(
                                        "The conclusion is nonnegativity of finite conditional entropy in nats. " +
                                        "As in the Shannon statement, no equality condition is claimed: this " +
                                        "theorem neither characterizes zero conditional entropy nor proves " +
                                        "strict positivity for non-degenerate conditional laws."))),
                DescribeRole.Theorem
            ))));
}
