using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.RenyiDivergence;

internal sealed class BasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Renyi divergence is defined for real orders and pinned by complementary half-order, self, and order-two identities.",
        H("Finite Renyi Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-renyi-divergence-is-the-logarithmic-power-sum"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/Basic.renyiDivergence"),
                H("Finite Renyi divergence is the logarithmic power sum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                    Colon, Eq,
                    Frac, Grp(D(1)), Grp(Alpha, Sp, Minus, D(1)),
                    Log, Sp, Open,
                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                    F.Id("p"), Open, F.Id("i"), Close,
                    Caret, Grp(Alpha, Sp), Sp,
                    F.Id("q"), Open, F.Id("i"), Close,
                    Caret, Grp(D(1), Minus, Alpha, Sp), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The repository already contains Kullback--Leibler divergence, the " +
                        "Bhattacharyya coefficient, and squared Hellinger distance as separate " +
                        "objects. The Renyi family places them in a common order parameter: order " +
                        "one half is the Bhattacharyya coefficient in logarithmic form, and hence " +
                        "is linked to squared Hellinger distance through the existing affinity " +
                        "identity, while the order-one limit is the classical divergence. This " +
                        "module introduces the finite family and proves the half-order bridge " +
                        "exactly.")),
                    Paragraph(Text(
                        "The order-one limit is not attempted. Establishing it requires a genuine " +
                        "limiting argument, so the present theorem set does not complete the " +
                        "unification suggested by the family.")),
                    Paragraph(Text(
                        "The definition is total. Lean totalizes real division, real powers at " +
                        "zero, and the logarithm at zero, and the order condition alpha != 1 " +
                        "therefore belongs to results that interpret the expression as a genuine " +
                        "Renyi divergence rather than to the data of the definition. Requiring a " +
                        "proof of alpha != 1 in the definition would alter every downstream " +
                        "signature; the interpreting theorems already constrain the order where " +
                        "that constraint is mathematically needed."))),
                DescribeRole.Definition
            ),
            Describe.Lean(
                DescribeId.Create("half-order-is-minus-twice-log-bhattacharyya"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/Basic.renyi_divergence_one_half"),
                H("Half order is minus twice log Bhattacharyya"),
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
                                    F.Id("D"), Underscore, Grp(Frac, Grp(D(1)), Grp(D(2))), Open,
                                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                                    Eq, Minus, D(2), Sp,
                                    Log, Sp, Open,
                                    Operatorname, Grp(F.Id("BC")), Open,
                                    F.Id("p"), Comma, Sp, F.Id("q"), Close, Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "At order one half both powers are square roots. Pointwise " +
                                        "nonnegativity of p is exactly the hypothesis used to combine them into " +
                                        "the frozen Bhattacharyya coefficient; no normalization, absolute " +
                                        "continuity, or nonnegativity assumption on q occurs in the theorem.")),
                                    Paragraph(Text(
                                        "The pinning argument is a coverage analysis: three corruptions were " +
                                        "hunted across three probes because no single identity observes every " +
                                        "part of the definition. Dropping the prefactor is detected here: on the " +
                                        "Bool point-mass-versus-uniform witness, the corrupted value is " +
                                        "-log(2)/2 rather than the correct log(2). That corruption nevertheless " +
                                        "survives self-divergence, where log(1) already forces zero. The order-two " +
                                        "witness cannot detect it either, since the correct prefactor " +
                                        "1/(alpha-1) equals one at alpha = 2.")),
                                    Paragraph(Text(
                                        "Swapping p and q in the two exponents exposes the complementary gap. It " +
                                        "survives the half-order bridge pointwise, because both exponents are one " +
                                        "half, and it also survives self-divergence. The order-two probe alone " +
                                        "separates the forms, returning -2 log(2) for the swapped expression " +
                                        "against the correct log(2).")),
                                    Paragraph(Text(
                                        "Replacing the exponent 1-alpha by alpha also survives the half-order " +
                                        "witness, but a uniform self-distribution at order two gives -3 log(2) " +
                                        "instead of zero. Thus a pinning identity can have a symmetry blind spot: " +
                                        "the half-order bridge is structurally incapable of detecting an exponent " +
                                        "swap. The order-two evaluation is therefore a necessary second probe at " +
                                        "a different order, not a decorative example. The caller independently " +
                                        "verified this blind spot."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("probability-mass-has-zero-self-divergence"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/Basic.renyi_divergence_self"),
                H("Probability mass has zero self-divergence"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                                    Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Colon, Sp,
                                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("p"), Open, F.Id("i"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Sp, Underscore, Grp(F.Id("i")), Sp,
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(1), Close,
                                    Sp, Rightarrow, RowBreak,
                                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("p"), Close,
                                    Eq, D(0), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "For a nonnegative normalized mass, the two powers recombine to p(i), so " +
                                        "the power sum is one and its logarithm vanishes. This is the self probe " +
                                        "used in the coverage analysis: at order two on the uniform Bool law it " +
                                        "rejects the alpha-in-both-exponents corruption.")),
                                    Paragraph(Text(
                                        "The theorem is stated for every real order because it is an identity of " +
                                        "the totalized formula. In particular, its alpha = 1 instance records " +
                                        "Lean's totalized value and is not an order-one limiting theorem. The " +
                                        "identical inputs have identical support, while nonnegativity and unit " +
                                        "mass ensure that the common support is nonempty."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("point-versus-uniform-has-order-two-divergence-log-two"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/Basic.renyi_divergence_two_point_order_two"),
                H("Point versus uniform has order-two divergence log two"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    F.Id("p"), Eq, Delta, Underscore,
                                    Grp(Operatorname, Grp(F.Id("true"))), Comma, Sp,
                                    F.Id("q"), Eq,
                                    F.Id("u"), Underscore, Grp(Operatorname, Grp(F.Id("Bool"))), Comma, RowBreak,
                                    F.Id("D"), Underscore, Grp(D(2)), Open,
                                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                                    Eq, Log, Sp, D(2), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The concrete Bool witness takes p to be the point mass at true and q to " +
                                        "be uniform. At order two the correct power sum is two, and the prefactor " +
                                        "is one, giving log(2). The reference law q is positive on both points, so " +
                                        "this evaluation lies in the finite-support regime rather than relying on " +
                                        "a zero denominator convention.")),
                                    Paragraph(Text(
                                        "Together with the half-order bridge and self-divergence, this evaluation " +
                                        "closes the coverage analysis. It supplies the distinct order needed to " +
                                        "break the exponent-swap symmetry that order one half cannot observe, " +
                                        "while its prefactor equal to one explains precisely why it cannot test " +
                                        "the presence of that prefactor."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("finite-renyi-divergence-is-nonnegative-below-order-one"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/Basic.renyi_divergence_nonneg"),
                H("Finite Renyi divergence is nonnegative below order one"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, Alpha, Sp, InMacro, Sp,
                                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                                    D(0), Lt, Alpha, Sp, Lt, D(1), Comma, RowBreak,
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
                                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(0), Close, Close,
                                    Sp, Rightarrow, RowBreak,
                                    D(0), Le, Sp,
                                    F.Id("D"), Underscore, Grp(Alpha, Sp), Open,
                                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "For 0 < alpha < 1 and two nonnegative normalized laws, weighted " +
                                        "arithmetic--geometric mean bounds the power sum above by one. Its " +
                                        "logarithm is therefore nonpositive, while 1/(alpha-1) is nonpositive, " +
                                        "and their product is nonnegative.")),
                                    Paragraph(Text(
                                        "This result additionally assumes discrete absolute continuity in the " +
                                        "direction q(i) = 0 implies p(i) = 0. Since p has unit mass, that support " +
                                        "condition supplies a coordinate on which both laws are positive and " +
                                        "thereby makes the power sum strictly positive. It is exactly the " +
                                        "hypothesis that excludes the disjoint-support flattening recorded " +
                                        "below."))),
                DescribeRole.Theorem
            ),
            Describe.Lean(
                DescribeId.Create("disjoint-support-is-flattened-by-totalization"),
                DeclarationHandle.Create("D5/S3/RenyiDivergence/Basic.renyi_divergence_disjoint_support_flattening_witness"),
                H("Disjoint support is flattened by totalization"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    F.Id("p"), Eq, Delta, Underscore,
                                    Grp(Operatorname, Grp(F.Id("true"))), Comma, Sp,
                                    F.Id("q"), Eq, Delta, Underscore,
                                    Grp(Operatorname, Grp(F.Id("false"))), Comma, RowBreak,
                                    F.Id("D"), Underscore, Grp(Frac, Grp(D(1)), Grp(D(2))), Open,
                                    F.Id("p"), Vert, Sp, Vert, Sp, F.Id("q"), Close,
                                    Eq, D(0), Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The two point masses are nonnegative and normalized but have disjoint " +
                                        "supports. They violate the absolute-continuity hypothesis q(i) = 0 " +
                                        "implies p(i) = 0 at true. At order one half every term in the power sum " +
                                        "vanishes, and Lean's Real.log(0) = 0 together with its Real.rpow " +
                                        "conventions returns zero.")),
                                    Paragraph(Text(
                                        "Mathematically the divergence is infinite in this case. The displayed " +
                                        "zero is a convention-induced flattening, not a mathematical claim about " +
                                        "disjoint probability laws. This qualification is itself frozen as a " +
                                        "theorem beside the finite results, so it cannot be mistaken for an " +
                                        "informal warning detached from the module it limits.")),
                                    Paragraph(Text(
                                        "The half-order bridge carries only nonnegativity of p and remains an " +
                                        "algebraic identity under the same totalized conventions. Self-divergence " +
                                        "carries a nonnegative normalized p with coincident support; the general " +
                                        "nonnegativity theorem carries both probability hypotheses, strict order " +
                                        "bounds, and absolute continuity; and the order-two point-versus-uniform " +
                                        "witness has an everywhere-positive q. These distinct support hypotheses " +
                                        "separate genuine finite interpretations from the frozen flattened " +
                                        "boundary value.")),
                                    Paragraph(Text(
                                        "This module opens the S3 RenyiDivergence bucket as the address for finite " +
                                        "Renyi divergences of real order alpha, their pinning identities, and " +
                                        "future monotonicity in the order. No order-one limit, monotonicity in " +
                                        "alpha, data-processing inequality for the family, or measure-theoretic " +
                                        "analogue is claimed. All logarithms are natural, so the units are nats."))),
                DescribeRole.Theorem
            ))));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
