using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class ChainRuleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Finite real-valued classical KL divergence decomposes into marginal and conditional terms.", H("Chain Rule for Finite Classical KL Divergence"), Blocks(
            Describe.Lean(DescribeId.Create("finite-classical-kl-divergence-obeys-the-chain-rule"), DeclarationHandle.Create("D5/S3/Divergence/ChainRule.kl_divergence_chain_rule"), H("Finite classical KL divergence obeys the chain rule"), StatementSource.FromAuthor(Disp(Seq(
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
                    F.Id("p"), Underscore, Grp(Iota), Open, F.Id("i"), Close,
                    Colon, Eq,
                    Sum, Underscore, Grp(F.Id("j")),
                    F.Id("p"), Open, F.Id("i"), Comma, F.Id("j"), Close,
                    Comma, Quad, Sp,
                    F.Id("q"), Underscore, Grp(Iota), Open, F.Id("i"), Close,
                    Colon, Eq,
                    Sum, Underscore, Grp(F.Id("j")),
                    F.Id("q"), Open, F.Id("i"), Comma, F.Id("j"), Close,
                    Comma, RowBreak,
                    F.Id("p"), Underscore, Grp(Kappa, Mid, Sp, F.Id("i")),
                    Open, F.Id("j"), Close, Colon, Eq,
                    Frac,
                    Grp(F.Id("p"), Open, F.Id("i"), Comma, F.Id("j"), Close),
                    Grp(F.Id("p"), Underscore, Grp(Iota), Open, F.Id("i"), Close),
                    Comma, Quad, Sp,
                    F.Id("q"), Underscore, Grp(Kappa, Mid, Sp, F.Id("i")),
                    Open, F.Id("j"), Close, Colon, Eq,
                    Frac,
                    Grp(F.Id("q"), Open, F.Id("i"), Comma, F.Id("j"), Close),
                    Grp(F.Id("q"), Underscore, Grp(Iota), Open, F.Id("i"), Close),
                    Semi, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                    D(0), Lt, F.Id("p"), Open,
                    F.Id("i"), Comma, Sp, F.Id("j"), Close,
                    Sp, Land, Sp,
                    D(0), Lt, F.Id("q"), Open,
                    F.Id("i"), Comma, Sp, F.Id("j"), Close, Close,
                    Sp, Rightarrow, RowBreak,
                    F.Id("D"), Open,
                    F.Id("p"), Vert, Vert, Sp, F.Id("q"), Close, Eq,
                    F.Id("D"), Open,
                    F.Id("p"), Underscore, Grp(Iota), Vert, Vert, Sp,
                    F.Id("q"), Underscore, Grp(Iota), Close, Plus, RowBreak,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("p"), Underscore, Grp(Iota), Open, F.Id("i"), Close,
                    F.Id("D"), Open,
                    F.Id("p"), Underscore, Grp(Kappa, Mid, Sp, F.Id("i")),
                    Vert, Vert, Sp,
                    F.Id("q"), Underscore, Grp(Kappa, Mid, Sp, F.Id("i")),
                    Close, Dot,
                    End, Grp(F.Id("gathered"))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "Let iota and kappa be finite types, and let p and q be strictly " +
                        "positive real functions on their product. Only strict positivity is " +
                        "assumed; neither p nor q is assumed normalized. The in-file " +
                        "definitions are marginal r i = sum_j r(i,j) and conditional r i j = " +
                        "r(i,j) / marginal r i, so the conditional is the genuine quotient.")),
                    Paragraph(Text(
                        "The empty second coordinate is handled explicitly in the Lean proof, " +
                        "so the theorem carries no Nonempty hypothesis and claims no " +
                        "normalization for an empty family. When kappa is nonempty, strict " +
                        "positivity makes every marginal positive, and sum_j conditional p i j " +
                        "= 1 is proved from these definitions and strict positivity, not " +
                        "assumed. The factorization p(i,j) = marginal p i * conditional p i j " +
                        "and Real.log_mul then split the finite joint sum into its marginal and " +
                        "marginal-weighted conditional terms.")),
                    Paragraph(Text(
                        "This is the finite real-valued klDivergence of ClassicalDPI, the " +
                        "repository's single source for the definition, not a measure-theoretic " +
                        "divergence. Mathlib's measure-valued " +
                        "InformationTheory.klDiv_compProd_eq_add is not used, and no bridge " +
                        "between the ENNReal measure divergence and this finite real sum is " +
                        "established here. The declaration therefore does not identify this " +
                        "finite divergence with any measure-valued KL divergence. The " +
                        "ninth-wave theorem D5/S3/Divergence/ProductAdditivity is the special " +
                        "case in which the conditionals do not depend on the first " +
                        "coordinate."))), DescribeRole.Theorem))));
}
