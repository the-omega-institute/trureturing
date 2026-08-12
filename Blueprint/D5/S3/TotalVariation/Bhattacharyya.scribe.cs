using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class BhattacharyyaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/TotalVariation/Bhattacharyya",
            "Finite Bhattacharyya affinity links total variation and relative entropy through the complementary Bretagnolle--Huber bound."),
        H("Bhattacharyya Affinity and the Bretagnolle--Huber Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-bhattacharyya-affinity-is-the-square-root-product-sum"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Bhattacharyya.bhattacharyya"),
                H("Finite Bhattacharyya affinity is the square-root product sum"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite real mass functions p and q, the Bhattacharyya coefficient, " +
                        "also called their Hellinger affinity, is the sum of the square roots of " +
                        "the coordinatewise products. The definition itself imposes no sign or " +
                        "normalization hypotheses; the probability assumptions enter the " +
                        "identities and inequalities below.")),
                    Paragraph(Text(
                        "This coefficient is the intermediate quantity that connects total " +
                        "variation to relative entropy. It also provides the natural intermediate " +
                        "for future comparisons with Hellinger distance and Renyi divergence, " +
                        "without defining either notion in the present module."))),
                DescribeRole.Definition
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("normalized-nonnegative-mass-has-self-affinity-one"),
                H("Normalized nonnegative mass has self-affinity one"),
                LeanTheorem(
                    "D5/S3/TotalVariation/Bhattacharyya.bhattacharyya_self"),
                Disp(Seq(
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
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("BC")), Open,
                    F.Id("p"), Comma, Sp, F.Id("p"), Close, Eq, D(1), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "A new definition must be pinned by identities: inequalities alone do " +
                        "not certify what has been defined. Self-affinity is the first pin. It " +
                        "rules out dropping the square root, because the resulting sum of p(i)^2 " +
                        "is 1/2 for the uniform law on Bool. It also rules out replacing the " +
                        "product by a sum, which gives sqrt(2) on a Bool point mass, and it rules " +
                        "out every incorrect constant factor c, which returns c rather than one.")),
                    Paragraph(Text(
                        "Self-affinity nevertheless does not determine the definition by itself. " +
                        "The one-sided corruption obtained by summing sqrt(p(i)p(i)) and ignoring " +
                        "q passes this identity perfectly. A single identity initially appeared " +
                        "sufficient and was not; the gap was found by actively seeking a " +
                        "corruption that survives the proposed pin, rather than by assuming that " +
                        "one identity must suffice.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("pointwise-disjoint-masses-have-zero-affinity"),
                H("Pointwise-disjoint masses have zero affinity"),
                LeanTheorem(
                    "D5/S3/TotalVariation/Bhattacharyya.bhattacharyya_eq_zero_of_mul_eq_zero"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("p"), Open, F.Id("i"), Close,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(0), Close,
                    Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("BC")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Eq, D(0), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Pointwise disjointness is the second pin. On two opposite Bool point " +
                        "masses, every product p(i)q(i) vanishes, so the true coefficient is zero. " +
                        "The one-sided corruption from the preceding discussion instead evaluates " +
                        "to one, because it sees only the self-affinity of p.")),
                    Paragraph(Text(
                        "Thus the second identity detects exactly the dependence on both inputs " +
                        "that self-affinity cannot test. The caller independently compiled both " +
                        "the surviving corruption and its refutation on the opposite-point-mass " +
                        "instance; the module freezes the refuting identity as a theorem rather " +
                        "than leaving the issue to an informal example.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("probability-affinity-is-at-most-one"),
                H("Probability affinity is at most one"),
                LeanTheorem(
                    "D5/S3/TotalVariation/Bhattacharyya.bhattacharyya_le_one"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("BC")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Le, Sp, D(1), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For two nonnegative normalized laws, finite Cauchy--Schwarz bounds the " +
                        "sum of sqrt(p(i))sqrt(q(i)) by the geometric mean of their total masses, " +
                        "which is one. This is an inequality associated with the pinned " +
                        "coefficient, not a substitute for either defining identity.")),
                    Paragraph(Text(
                        "Both laws are nonnegative and normalized in this statement. These are " +
                        "exactly the hypotheses used to identify the two squared Euclidean norms " +
                        "with unit mass.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("total-variation-square-is-controlled-by-affinity"),
                H("Total variation square is controlled by affinity"),
                LeanTheorem(
                    "D5/S3/TotalVariation/Bhattacharyya.total_variation_sq_le_one_sub_bhattacharyya_sq"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Caret, Grp(D(2)), Le, Sp,
                    D(1), Minus,
                    Operatorname, Grp(F.Id("BC")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Caret, Grp(D(2)), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "This is the first bridge in the final proof. Factoring each absolute " +
                        "difference through sqrt(p(i))-sqrt(q(i)) and " +
                        "sqrt(p(i))+sqrt(q(i)), and then applying finite Cauchy--Schwarz, yields " +
                        "TV(p,q)^2 <= 1-BC(p,q)^2.")),
                    Paragraph(Text(
                        "The calculation uses both probability laws in full: p and q must each " +
                        "be coordinatewise nonnegative and normalized to total mass one. Their " +
                        "normalizations evaluate the squared sums that arise after " +
                        "Cauchy--Schwarz.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("negative-divergence-exponential-is-controlled-by-affinity"),
                H("Negative-divergence exponential is controlled by affinity"),
                LeanTheorem(
                    "D5/S3/TotalVariation/Bhattacharyya.exp_neg_kl_divergence_le_bhattacharyya_sq"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(0), Sp,
                    Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(0), Close,
                    Sp, Rightarrow, RowBreak,
                    Exp, Sp, Open, Minus,
                    F.Id("D"), Open, F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close,
                    Close, Le, Sp,
                    Operatorname, Grp(F.Id("BC")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Caret, Grp(D(2)), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "This is the second bridge. Jensen's inequality is applied with p as the " +
                        "normalized system of weights to the logarithm of sqrt(q(i)/p(i)) on the " +
                        "positive support of p. Exponentiation then gives " +
                        "exp(-D(p||q)) <= BC(p,q)^2.")),
                    Paragraph(Text(
                        "Its hypotheses are deliberately asymmetric. The law p is nonnegative " +
                        "and normalized, whereas q is required only to be nonnegative; the " +
                        "argument never uses the total mass of q. The logarithm instead forces " +
                        "the repository's discrete absolute-continuity convention q(i)=0 implies " +
                        "p(i)=0, which makes every ratio on the positive support of p strictly " +
                        "positive.")),
                    Paragraph(Text(
                        "The first bridge needs two normalized laws, while the second needs only " +
                        "one normalized law and a nonnegative reference mass. These hypothesis " +
                        "sets were derived statement by statement rather than copied from the " +
                        "final theorem, continuing the standing practice in this bucket across " +
                        "five waves.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("bretagnolle-huber-complements-pinsker"),
                H("Bretagnolle--Huber complements Pinsker"),
                LeanTheorem(
                    "D5/S3/TotalVariation/Bhattacharyya.bretagnolle_huber"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1), Close,
                    Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(0), Sp,
                    Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(0), Close,
                    Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Le, Sp,
                    Sqrt, Sp, Grp(
                        D(1), Minus,
                        Exp, Sp, Open, Minus,
                        F.Id("D"), Open, F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close,
                        Close), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The proof is the direct composition of the two bridges. The first gives " +
                        "TV(p,q)^2 <= 1-BC(p,q)^2, and the Jensen bridge gives " +
                        "exp(-D(p||q)) <= BC(p,q)^2. Substitution, nonnegativity of relative " +
                        "entropy, and monotonicity of the square root yield the displayed bound.")),
                    Paragraph(Text(
                        "This bound exists because Pinsker and Bretagnolle--Huber govern different " +
                        "regimes. Pinsker gives 2 TV(p,q)^2 <= D(p||q), equivalently " +
                        "TV(p,q) <= sqrt(D(p||q)/2). At divergence two it recovers only the " +
                        "universal bound one, and above two it permits an upper bound greater than " +
                        "one even though total variation never exceeds one. It is therefore " +
                        "vacuous for D(p||q) >= 2 as an improvement over the probability unit " +
                        "bound.")),
                    Paragraph(Text(
                        "By contrast, the Bretagnolle--Huber right side is strictly below one for " +
                        "every finite divergence and approaches one only as the divergence tends " +
                        "to infinity. The inequalities are complementary, not redundant: Pinsker " +
                        "is sharper for small divergence, whereas Bretagnolle--Huber continues to " +
                        "give nontrivial information when the laws are far apart. All logarithms " +
                        "are natural, so divergence is measured in nats.")))),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("bretagnolle-huber-is-strict-on-a-bool-witness"),
                H("Bretagnolle--Huber is strict on a Bool witness"),
                LeanTheorem(
                    "D5/S3/TotalVariation/Bhattacharyya.bretagnolle_huber_strict_witness"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    F.Id("p"), Eq, Delta, Underscore,
                    Grp(Operatorname, Grp(F.Id("true"))), Comma, Sp,
                    F.Id("q"), Eq,
                    F.Id("u"), Underscore, Grp(Operatorname, Grp(F.Id("Bool"))), Comma, RowBreak,
                    Operatorname, Grp(F.Id("TV")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Lt,
                    Sqrt, Sp, Grp(
                        D(1), Minus,
                        Exp, Sp, Open, Minus,
                        F.Id("D"), Open, F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close,
                        Close), Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The strictness claim is itself a theorem in the formal module. The " +
                        "concrete Bool instance takes p to be the point mass at true and q to be " +
                        "the uniform law. Lean computes total variation as 1/2 and relative " +
                        "entropy as log(2), reducing the strict inequality to " +
                        "1/2 < sqrt(1/2). Thus non-equality is machine-checked and frozen rather " +
                        "than asserted in a comment or inferred from a numerical approximation.")),
                    Paragraph(Text(
                        "The TotalVariation bucket now contains Pinsker's bound, the metric laws " +
                        "with the attained variational characterization, data-processing " +
                        "contraction, and the complementary Bretagnolle--Huber bound with its " +
                        "Bhattacharyya coefficient. The coefficient is a natural bridge for " +
                        "future Hellinger and Renyi comparisons. No Hellinger distance, Renyi " +
                        "divergence, equality analysis of either bound, measure-theoretic " +
                        "analogue, or other extension is claimed here.")))))));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
