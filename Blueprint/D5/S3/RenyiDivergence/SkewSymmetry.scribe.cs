using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.RenyiDivergence;

internal sealed class SkewSymmetryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Renyi divergence obeys alpha-complement skew symmetry, with exact endpoint residues and an unconditional form away from orders zero and one.",
        H("Skew Symmetry of Finite Renyi Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("renyi-divergence-has-alpha-complement-skew-symmetry"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_skew_symmetry"),
                H("Renyi divergence has alpha-complement skew symmetry"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Alpha, Eq, D(1), Sp, Rightarrow, Sp,
                    Log, Sp, Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Close,
                    Eq, Sp, D(0), Close,
                    Sp, Land, Sp, RowBreak,
                    Open, Alpha, Eq, D(0), Sp, Rightarrow, Sp,
                    Log, Sp, Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Close,
                    Eq, Sp, D(0), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    Open, Alpha, Minus, D(1), Close, Sp, Star, Sp,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Eq, Sp, Minus, Alpha, Sp, Star, Sp,
                    F.Id("D"), Underscore, Grp(D(1), Minus, Alpha, Sp), Open,
                    F.Id("q"), Vert, Sp, Vert, Sp, F.Id("p"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The primary duality statement is a product identity. Multiplication by " +
                        "alpha - 1 on one side and by -alpha on the other avoids dividing at either " +
                        "exceptional order, while exchanging the laws and replacing alpha by " +
                        "1 - alpha.")),
                    Paragraph(Text(
                        "The endpoint assumptions record exactly what Lean's totalized definition " +
                        "forces. At alpha = 1 the residue is log(sum p), and at alpha = 0 it is " +
                        "log(sum q). These conditions are weaker than normalization: unit total " +
                        "mass satisfies them through log 1 = 0, but zero total mass also satisfies " +
                        "them because Lean's Real.log 0 = 0.")),
                    Paragraph(Text(
                        "Away from the endpoint cases, the two finite power sums agree termwise after " +
                        "commuting multiplication and simplifying the complementary exponent. No " +
                        "sign, support, or normalization property is used in that algebraic step.")),
                    Paragraph(Text(
                        "Complementation maps the interval 0 < alpha < 1 onto itself. It sends " +
                        "alpha > 1 to the negative order 1 - alpha, outside the range of the frozen " +
                        "sub-unit data-processing theorem. This identity therefore does not mirror " +
                        "that theorem into an above-one data-processing inequality; that gap remains " +
                        "open."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("normalized-laws-have-alpha-complement-skew-symmetry-at-every-order"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_skew_symmetry_of_normalized"),
                H("Normalized laws have alpha-complement skew symmetry at every order"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, Sp, D(1),
                    Sp, Land, Sp,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, Sp, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Open, Alpha, Minus, D(1), Close, Sp, Star, Sp,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Eq, Sp, Minus, Alpha, Sp, Star, Sp,
                    F.Id("D"), Underscore, Grp(D(1), Minus, Alpha, Sp), Open,
                    F.Id("q"), Vert, Sp, Vert, Sp, F.Id("p"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "If both finite laws have unit total mass, the product-form identity holds " +
                        "at every real order. No pointwise nonnegativity or strict positivity " +
                        "assumption is needed; normalization is used only to discharge the two " +
                        "possible endpoint logarithms as log 1.")),
                    Paragraph(Text(
                        "This is a sufficient specialization of the exact endpoint theorem, not a " +
                        "characterization of all admissible laws. In particular, the preceding " +
                        "zero-total-mass possibility shows why replacing the endpoint conditions by " +
                        "normalization would state a stronger hypothesis than the proof requires.")),
                    Paragraph(Text(
                        "The conclusion remains in product form at alpha = 0 and alpha = 1. It does " +
                        "not identify the totalized order-one value with Kullback--Leibler divergence " +
                        "and asserts no limiting statement."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("away-from-zero-and-one-skew-symmetry-is-unconditional"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_skew_symmetry_of_ne_zero_one"),
                H("Away from zero and one, skew symmetry is unconditional"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, Alpha, Neq, Sp, D(0), Sp, Land, Sp,
                    Alpha, Neq, Sp, D(1), Close, Sp, Rightarrow, RowBreak,
                    Open, Alpha, Minus, D(1), Close, Sp, Star, Sp,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Eq, Sp, Minus, Alpha, Sp, Star, Sp,
                    F.Id("D"), Underscore, Grp(D(1), Minus, Alpha, Sp), Open,
                    F.Id("q"), Vert, Sp, Vert, Sp, F.Id("p"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When alpha differs from both zero and one, the endpoint obligations are " +
                        "vacuous and product-form skew symmetry is purely algebraic. The functions p " +
                        "and q are completely arbitrary finite real-valued functions: the theorem " +
                        "requires no normalization, nonnegativity, positivity, support condition, or " +
                        "other hypothesis on either one.")),
                    Paragraph(Text(
                        "This unrestricted statement includes sub-unit, super-unit, and negative " +
                        "orders other than zero and one. Its breadth comes from retaining each base " +
                        "and exponent in the same term while only reversing the product, so the " +
                        "totalized behavior of Real.rpow at a zero base creates no extra case.")),
                    Paragraph(Text(
                        "The absence of assumptions on p and q does not enlarge the range of the " +
                        "frozen data-processing result. For a super-unit alpha, the dual order is " +
                        "negative, and no data-processing inequality at that dual order has been " +
                        "proved here."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("renyi-divergence-equals-its-scaled-dual"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_eq_scaled_dual"),
                H("Renyi divergence equals its scaled dual"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Alpha, Neq, Sp, D(1), Sp, Land, Sp,
                    Open, Alpha, Eq, D(0), Sp, Rightarrow, Sp,
                    Log, Sp, Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Close,
                    Eq, Sp, D(0), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Eq, Sp,
                    Frac, Grp(Alpha), Grp(D(1), Minus, Alpha), Sp, Star, Sp,
                    F.Id("D"), Underscore, Grp(D(1), Minus, Alpha, Sp), Open,
                    F.Id("q"), Vert, Sp, Vert, Sp, F.Id("p"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Solving the product identity for its first divergence gives the familiar " +
                        "scaled-dual form with factor alpha/(1 - alpha). This division excludes " +
                        "alpha = 1, which is why the solved form is secondary to the endpoint-safe " +
                        "product identity.")),
                    Paragraph(Text(
                        "Order zero remains within the statement. At that order the exact condition " +
                        "log(sum q) = 0 is still required by the totalized definition; no condition " +
                        "on the total mass of p is introduced. Away from zero, this remaining endpoint " +
                        "premise is vacuous.")),
                    Paragraph(Text(
                        "The displayed equality is an algebraic rearrangement under a nonzero " +
                        "denominator. It supplies neither an order-one continuation nor a route from " +
                        "the frozen below-one data-processing inequality to an above-one theorem."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("half-order-renyi-divergence-is-symmetric"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_one_half_symmetry"),
                H("Half-order Renyi divergence is symmetric"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    F.Id("D"), Underscore,
                    Grp(Frac, Grp(D(1)), Grp(D(2)), Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Eq, Sp,
                    F.Id("D"), Underscore,
                    Grp(Frac, Grp(D(1)), Grp(D(2)), Sp), Open,
                    F.Id("q"), Vert, Sp, Vert, Sp, F.Id("p"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The order one half is fixed by alpha complementation. Specializing the " +
                        "unconditional away-from-endpoints identity therefore makes the two scalar " +
                        "factors equal and yields symmetry under exchange of p and q.")),
                    Paragraph(Text(
                        "No hypothesis on either finite real-valued function is needed. This theorem " +
                        "is a specialization of the product identity rather than a second expansion " +
                        "of the Renyi definition or an appeal to symmetry of another coefficient.")),
                    Paragraph(Text(
                        "Self-duality is specific to order one half within the alpha-complement map. " +
                        "The result does not assert symmetry at general order."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("half-order-dual-renyi-divergence-equals-the-bhattacharyya-expression"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/SkewSymmetry.renyi_divergence_one_half_dual_eq_bhattacharyya"),
                H("The half-order dual Renyi divergence equals the Bhattacharyya expression"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                    Sp, Rightarrow, RowBreak,
                    F.Id("D"), Underscore,
                    Grp(Frac, Grp(D(1)), Grp(D(2)), Sp), Open,
                    F.Id("q"), Vert, Sp, Vert, Sp, F.Id("p"), Close,
                    Eq, Sp, Minus, D(2), Sp, Star, Sp, Log, Sp, Open,
                    Operatorname, Grp(F.Id("bhattacharyya")), Open,
                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The dual orientation at order one half agrees with the frozen " +
                        "Bhattacharyya link: D one half of q relative to p equals minus twice the " +
                        "logarithm of the Bhattacharyya coefficient written in the p, q orientation. " +
                        "The differing orientations make this a direct consistency check between the " +
                        "two frozen notions.")),
                    Paragraph(Text(
                        "Only pointwise nonnegativity of p is assumed. The frozen Bhattacharyya " +
                        "identity is applied once in the p, q orientation, and half-order symmetry " +
                        "then exchanges the divergence arguments. Consequently no nonnegativity, " +
                        "normalization, positivity, or support premise on q is needed.")),
                    Paragraph(Text(
                        "This cross-check does not strengthen the frozen Bhattacharyya theorem beyond " +
                        "its stated hypothesis, and it supplies no new data-processing or limiting " +
                        "result."))),
                DescribeRole.Theorem
            )
        )));
}
