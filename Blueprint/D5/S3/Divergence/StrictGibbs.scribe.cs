using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class StrictGibbsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Distinct finite probability mass functions have strictly positive classical KL divergence.", H("Strict Positivity of Finite Classical KL Divergence"), Blocks(
            Describe.Lean(DescribeId.Create("distinct-finite-probability-masses-have-positive-kl-divergence"), DeclarationHandle.Create("D5/S3/Divergence/StrictGibbs.kl_divergence_pos_of_ne"), H("Distinct finite probability masses have positive KL divergence"), StatementSource.FromAuthor(Disp(Seq(
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
                    Close, Sp, Rightarrow, RowBreak,
                    Open,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Le, Sp, F.Id("q"), Open, F.Id("i"), Close, Close,
                    Sp, Land, Sp,
                    Sum, Underscore, Grp(F.Id("i")),
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(1),
                    Close, Sp, Rightarrow, RowBreak,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("q"), Open, F.Id("i"), Close, Eq, D(0),
                    Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("i"), Close, Eq, D(0), Close,
                    Sp, Rightarrow, RowBreak,
                    F.Id("p"), Neq, Sp, F.Id("q"),
                    Sp, Rightarrow, RowBreak,
                    D(0), Lt,
                    F.Id("D"), Open,
                    F.Id("p"), Vert, Sp, F.Id("q"), Close, Dot,
                    End, Grp(F.Id("gathered"))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text(
                        "Let I be a finite alphabet. Strict Gibbs assumes nonnegativity, " +
                        "normalization, and discrete absolute continuity; it does not assume " +
                        "strict positivity. This is deliberately different from the channel-side " +
                        "convention used by StrictDpi, so the binders must not be copied between " +
                        "the two modules.")),
                    Paragraph(Text(
                        "The difference is forced by the formulas: StrictGibbs never divides, so " +
                        "discrete absolute continuity alone is enough to keep every logarithm " +
                        "meaningful. StrictDpi forms posteriors by quotienting by channelOutput W " +
                        "p y and therefore needs that denominator to be positive; the same applies " +
                        "to q.")),
                    Paragraph(Text(
                        "This theorem composes " +
                        "D5/S3/Divergence/GrandmotherTheorem.kl_divergence_nonneg with " +
                        "D5/S3/Divergence/GibbsEquality.kl_divergence_eq_zero_iff; nothing is " +
                        "re-proved. The first result supplies the nonnegative lower bound, and " +
                        "the second rules out equality at zero when p and q are distinct.")),
                    Paragraph(Text(
                        "It closes the gap that GrandmotherTheorem's own document names: " +
                        "GrandmotherTheorem's own document records only nonnegativity and adds no " +
                        "equality characterization. The new theorem records the strict consequence " +
                        "for distinct mass functions without reopening either proof.")),
                    Paragraph(Text(
                        "The divergence here is the finite real-valued klDivergence of " +
                        "ClassicalDPI, not a measure-theoretic divergence. Its domain is a finite " +
                        "type and its values are real numbers; no measure-valued or ENNReal bridge " +
                        "is claimed."))), DescribeRole.Theorem))));
}
