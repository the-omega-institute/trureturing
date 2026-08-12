using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class PinskerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite total variation is pinned by an equal-mass identity and bounded by relative entropy in nats.",
        H("Finite Total Variation and Pinsker's Inequality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-total-variation-is-half-l1-distance"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Pinsker.totalVariation"),
                H("Finite total variation is half the L1 distance"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Colon, Eq, Frac, Grp(D(1)), Grp(D(2)),
                    Sum, Underscore, Grp(F.Id("i")),
                    Vert, Sp, F.Id("p"), Open, F.Id("i"), Close, Minus,
                    F.Id("q"), Open, F.Id("i"), Close, Sp, Vert, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite real mass functions p and q, totalVariation is one half " +
                        "of the sum of the absolute coordinate differences. It uses the " +
                        "probability-theory normalization in which disjoint " +
                        "unit point masses have distance one.")),
                    Paragraph(Text(
                        "Pinsker's inequality cannot by itself certify this definition. The " +
                        "inequality 2 TV(p,q)^2 <= D(p||q) would remain valid if the factor one " +
                        "half were corrupted in the safe direction, or if TV were " +
                        "replaced by any uniformly smaller quantity. The normalization and the " +
                        "absolute-value structure are therefore pinned by an identity, not by " +
                        "the later inequality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("equal-mass-total-variation-is-positive-excess"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Pinsker.total_variation_eq_sum_positive"),
                H("Equal-mass total variation is positive excess"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("p"), Open, F.Id("i"), Close, Eq,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("q"), Open, F.Id("i"), Close,
                    Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Eq, Sum, Underscore,
                    Grp(F.Id("i"), Colon, Sp,
                        F.Id("q"), Open, F.Id("i"), Close, Le, Sp,
                        F.Id("p"), Open, F.Id("i"), Close),
                    Open, F.Id("p"), Open, F.Id("i"), Close, Minus,
                    F.Id("q"), Open, F.Id("i"), Close, Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This identity is the methodological pin for the definition. Equal " +
                        "total mass makes the signed differences sum to zero, so the positive " +
                        "part on the dominance set q(i) <= p(i) balances the negative part on " +
                        "its complement. Consequently, half the absolute sum is exactly the " +
                        "positive excess displayed above.")),
                    Paragraph(Text(
                        "The hypothesis is minimal in the precise sense expressed by the Lean " +
                        "signature: only equality of total mass is assumed. Neither p nor q is " +
                        "required to be nonnegative, and their common mass need not be one.")),
                    Paragraph(Text(
                        "A concrete Bool witness shows that the pin is substantive. For two " +
                        "disjoint unit point masses, the raw L1 sum is 2 while the positive " +
                        "excess is 1. A proposed normalization constant c must therefore satisfy " +
                        "2c = 1, hence c = 1/2. Dropping the absolute values produces the signed " +
                        "total 0, while reversing the dominance set produces the negative excess " +
                        "-1; both corruptions fail the identity. This witness was compiled " +
                        "independently of the formal proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-pinsker-carries-the-analytic-content"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Pinsker.binary_pinsker"),
                H("Binary Pinsker carries the analytic content"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), InMacro,
                    OpenBracket, D(0), Comma, Sp, D(1), CloseBracket, Comma, RowBreak,
                    Open, F.Id("b"), Eq, D(0), Sp, Rightarrow, Sp, F.Id("a"), Eq, D(0), Close,
                    Sp, Land, Sp,
                    Open, D(1), Minus, F.Id("b"), Eq, D(0), Sp, Rightarrow, Sp,
                    D(1), Minus, F.Id("a"), Eq, D(0), Close,
                    Sp, Rightarrow, RowBreak,
                    D(2), Open, F.Id("a"), Minus, F.Id("b"), Close,
                    Caret, Grp(D(2)), Le, Sp,
                    F.Id("a"), Log, Open, Frac, Grp(F.Id("a")), Grp(F.Id("b")), Close,
                    Plus, Open, D(1), Minus, F.Id("a"), Close,
                    Log, Open,
                    Frac, Grp(D(1), Minus, F.Id("a")), Grp(D(1), Minus, F.Id("b")),
                    Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This two-point scalar theorem is where the genuine analytic content of " +
                        "Pinsker's inequality resides. The proof treats the endpoint cases first " +
                        "and, on the open unit interval, proves convexity of the divergence " +
                        "deficit after subtracting 2(a-b)^2. Its first derivative vanishes at b, " +
                        "so convexity yields the stated lower bound.")),
                    Paragraph(Text(
                        "The two implication hypotheses are discrete absolute continuity at " +
                        "both endpoints. The condition b = 0 implies a = 0 controls the first " +
                        "atom, while 1-b = 0 implies 1-a = 0 controls the complementary atom. " +
                        "Both are required because a two-point reference law can degenerate at " +
                        "either end."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-support-data-processing-is-an-identity-corollary"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Pinsker.kl_divergence_channel_le_zero_support"),
                H("Zero-support data processing is an identity corollary"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("X"), Comma, Sp, F.Id("Y"), Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("X"), Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, F.Id("Y"), Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp, F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    F.Id("X"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    F.Id("W"), Colon, Sp,
                    F.Id("X"), To, Sp, F.Id("Y"), To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("x")), F.Id("p"), Open, F.Id("x"), Close,
                    Eq, D(1), Close, Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("x")), F.Id("q"), Open, F.Id("x"), Close,
                    Eq, D(1), Close, Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    F.Id("q"), Open, F.Id("x"), Close, Eq, D(0), Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("x"), Close, Eq, D(0), Close, Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    D(0), Le, Sp, F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Close, Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    Sum, Underscore, Grp(F.Id("y")),
                    F.Id("W"), Open, F.Id("x"), Comma, Sp, F.Id("y"), Close,
                    Eq, D(1), Close, Close,
                    Sp, Rightarrow, RowBreak,
                    F.Id("D"), Open, F.Id("W"), F.Id("p"), Vert, Vert, Sp,
                    F.Id("W"), F.Id("q"), Close, Le, Sp,
                    F.Id("D"), Open, F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "This theorem is not an independent reproof of data processing. It is " +
                        "derived by rewriting with the already-frozen " +
                        "classical_dpi_identity_zero_support from D5/S3/DivergenceSupport and " +
                        "then proving that the residual sum of output-weighted posterior " +
                        "divergences is nonnegative. That identity was contributed separately.")),
                    Paragraph(Text(
                        "The new content is precisely that residual nonnegativity under the " +
                        "repository's zero-support convention. The DivergenceSupport module " +
                        "established the identity and treated the degenerate case in which the " +
                        "output weight vanishes; it did not establish nonnegativity of the full " +
                        "residual. Here a positive output weight yields normalized nonnegative " +
                        "posteriors with inherited absolute continuity, to which the frozen " +
                        "Gibbs inequality applies.")),
                    Paragraph(Text(
                        "This provenance is required by the repository's one-source-of-truth " +
                        "discipline. A later inequality that follows from an earlier identity is " +
                        "presented as its corollary, not as a rival proof of the same structure.")),
                    Paragraph(Text(
                        "Although this is a general divergence statement rather than a " +
                        "total-variation statement, it remains in this bucket because it " +
                        "currently has exactly one consumer: the assembly below. The repository " +
                        "lifts an abstraction when a second instance or demonstrated pressure " +
                        "appears, not in anticipation. A second consumer should therefore cause " +
                        "this lemma to be lifted to DivergenceSupport."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pinsker-reduces-through-the-dominance-channel"),
                DeclarationHandle.Create("D5/S3/TotalVariation/Pinsker.pinsker_inequality"),
                H("Pinsker reduces through the dominance channel"),
                StatementSource.FromAuthor(Disp(Seq(
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
                    Sum, Underscore, Grp(F.Id("i")), F.Id("p"), Open, F.Id("i"), Close,
                    Eq, D(1), Close, Sp, Land, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i")), F.Id("q"), Open, F.Id("i"), Close,
                    Eq, D(1), Close, Sp, Land, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(0), Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(0), Close,
                    Sp, Rightarrow, RowBreak,
                    D(2), Operatorname, Grp(F.Id("TV")), Open, F.Id("p"), Comma, Sp, F.Id("q"), Close,
                    Caret, Grp(D(2)), Le, Sp,
                    F.Id("D"), Open, F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The proof has three layers. First, binary_pinsker supplies the genuine " +
                        "analytic estimate on two points. Second, data processing sends p and q " +
                        "through the deterministic channel i maps to the truth value of " +
                        "q(i) <= p(i), reducing the finite alphabet to Bool. Third, the assembly " +
                        "identifies the two output masses, applies the binary estimate, and " +
                        "returns through the data-processing inequality.")),
                    Paragraph(Text(
                        "If a and b denote the p- and q-masses of the dominance set, the pinning " +
                        "identity gives TV(p,q) = a-b. The Bool output divergence is exactly the " +
                        "binary expression, and zero-support data processing bounds it above by " +
                        "D(p||q). Thus the channel layer performs the reduction, while the scalar " +
                        "layer carries the analytic work.")),
                    Paragraph(Text(
                        "The absolute-continuity convention is q(i) = 0 implies p(i) = 0, exactly " +
                        "as in the frozen divergence modules. It is preserved by the channel and " +
                        "induces both endpoint implications required by binary_pinsker.")),
                    Paragraph(Text(
                        "This document opens the TotalVariation bucket at stratum S3. The bucket " +
                        "is split from D5/S3/Entropy, which had reached its twelve-file capacity. " +
                        "All logarithms are natural, so the divergence and the bound are in nats.")),
                    Paragraph(Text(
                        "No reverse bound of Bretagnolle-Huber type is claimed. The module gives " +
                        "no continuous or measure-theoretic analogue and no analysis of sharpness " +
                        "or equality cases."))),
                DescribeRole.Theorem))));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
