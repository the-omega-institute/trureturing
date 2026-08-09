using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class MarginalMonotoneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Divergence/MarginalMonotone",
            "Taking the first-coordinate marginal cannot increase finite real-valued classical KL divergence."),
        H("Marginal Monotonicity of Finite Classical KL Divergence"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("first-coordinate-marginal-does-not-increase-finite-classical-kl-divergence"),
                H("The first-coordinate marginal does not increase finite classical KL divergence"),
                LeanTheorem(
                    "D5/S3/Divergence/MarginalMonotone.kl_divergence_marginal_le"),
                Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                    CloseBracket, Sp,
                    OpenBracket,
                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                    CloseBracket, Comma, RowBreak,
                    Forall, Sp,
                    F.Id("p"), Comma, Sp, F.Id("q"), Colon, Sp,
                    Iota, Times, Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                    D(0), Lt, F.Id("p"), Open,
                    F.Id("i"), Comma, F.Id("j"), Close,
                    Sp, Land, Sp,
                    D(0), Lt, F.Id("q"), Open,
                    F.Id("i"), Comma, F.Id("j"), Close, Close,
                    Sp, Rightarrow, RowBreak,
                    F.Id("D"), Open,
                    F.Id("p"), Underscore, Grp(Iota), Vert, Vert, Sp,
                    F.Id("q"), Underscore, Grp(Iota), Close,
                    Sp, Le, Sp,
                    F.Id("D"), Open,
                    F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "Let iota and kappa be finite types, and let p and q be strictly " +
                        "positive real functions on their product. Only strict positivity of " +
                        "p and q is assumed; no normalization of either joint function is " +
                        "assumed.")),
                    Paragraph(Text(
                        "This theorem is a composition of two repository results. The wave-10 " +
                        "chain rule D5/S3/Divergence/ChainRule.kl_divergence_chain_rule supplies " +
                        "the exact decomposition of joint divergence into the first-coordinate " +
                        "marginal divergence plus a marginal-weighted sum of conditional " +
                        "divergences. The Grandmother theorem " +
                        "D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg supplies " +
                        "nonnegativity of each conditional divergence, and Finset.sum_nonneg " +
                        "combines those pointwise bounds.")),
                    Paragraph(Text(
                        "The Grandmother theorem's normalization premises are discharged, not " +
                        "assumed: for every first coordinate, both conditionals sum to one, " +
                        "proved directly from the definitions. Its absolute-continuity premise " +
                        "is trivial here because both conditionals are strictly positive. The " +
                        "empty second coordinate is handled explicitly, so the theorem carries " +
                        "no Nonempty hypothesis.")),
                    Paragraph(Text(
                        "This is the finite real-valued klDivergence of ClassicalDPI, the " +
                        "repository's single source for the definition, not a measure-theoretic " +
                        "divergence. Mathlib's InformationTheory.klDiv_compProd_eq_add is not " +
                        "used, and no ENNReal/finite-sum bridge is established here.")),
                    Paragraph(Text(
                        "This module claims monotonicity only under taking the first-coordinate " +
                        "marginal; it does not claim a general data-processing inequality over " +
                        "arbitrary channels.")))))));
}
