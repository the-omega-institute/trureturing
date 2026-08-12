using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.TotalVariation;

internal sealed class IndependentSamplingExponentialBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A repeated failure factor is at most its exponential envelope on the probability interval.",
        H("Exponential Bound for Repeated Failure Factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-repeated-failure-factor-has-an-exponential-envelope"),
                DeclarationHandle.Create(
                    "D5/S3/TotalVariation/IndependentSamplingExponentialBound.independent_sampling_exponential_bound"),
                H("A repeated failure factor has an exponential envelope"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, Varepsilon, Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("m"), Sp, InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, RowBreak,
                    Open, D(0), Le, Sp, Varepsilon, Sp, Land, Sp,
                    Varepsilon, Sp, Le, Sp, D(1), Close,
                    Sp, Rightarrow, Sp, RowBreak,
                    Open, D(1), Minus, Varepsilon, Close, Caret, Grp(F.Id("m")),
                    Sp, Le, Sp,
                    Exp, Sp, Open, Minus, Varepsilon, Sp, F.Id("m"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a probability threshold epsilon and a natural sample count m, the "
                        + "m-fold factor (1-epsilon)^m is no larger than exp(-epsilon m). The two "
                        + "displayed assumptions record exactly that epsilon lies in the closed "
                        + "probability interval.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched first for one-subtraction exponential bounds "
                        + "and natural powers of the real exponential. The exact library results "
                        + "Real.one_sub_le_exp_neg and Real.exp_nat_mul were found. The proof is a "
                        + "thin wrapper: it raises the first inequality to m using nonnegativity of "
                        + "1-epsilon, then rewrites the resulting power with the second result.")),
                    Paragraph(Text(
                        "This is an honest partial closure of only the second inequality in the "
                        + "recovery clause of the source theorem. It does not formalize the preceding "
                        + "probability inequality, independent-sampling semantics, the distribution-"
                        + "match caveat, the co-selection collapse clause, or the final phase-change "
                        + "interpretation. Those source subitems remain unresolved.")),
                    Paragraph(Text(
                        "The nonnegativity assumption on epsilon records the source probability "
                        + "domain, although the elementary upper estimate itself only needs epsilon "
                        + "at most one. No event space, random variable, or probability law is "
                        + "introduced by this analytic partial closure."))),
                DescribeRole.Theorem)),
        []));
}
