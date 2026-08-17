using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Repulsion;

internal sealed class RepulsionMaximumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive rational repulsion profile has an attained square-root maximum.",
        H("Exact Maximum of a Rational Repulsion Profile"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-rational-repulsion-profile-has-exact-maximum"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Repulsion/RepulsionMaximum."
                    + "repulsion_profile_has_exact_maximum"),
                H("The rational repulsion profile has an exact attained maximum"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp, F.Id("u"),
                    Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                    D(0), Sp, Lt, Sp, F.Id("b"), Sp, Lt, Sp, F.Id("a"),
                    Sp, Land, Sp, D(0), Sp, Lt, Sp, F.Id("u"), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("IsGreatest")), Open,
                    Left, OpenBrace,
                    Frac, Grp(F.Id("a")), Grp(F.Id("w"), Sp, Plus, Sp, F.Id("u")),
                    Sp, Minus, Sp, Frac, Grp(F.Id("b")), Grp(F.Id("w")),
                    Sp, Mid, Sp, F.Id("w"), Sp, Gt, Sp, D(0),
                    Right, CloseBrace, Comma, Esc,
                    Frac,
                    Grp(Open, Sqrt, Grp(F.Id("a")), Sp, Minus, Sp,
                        Sqrt, Grp(F.Id("b")), Close, Caret, Grp(D(2))),
                    Grp(F.Id("u")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive b below a and positive u, every value of the profile "
                        + "a/(w+u) - b/w at positive w is bounded above by "
                        + "(sqrt(a)-sqrt(b))^2/u, and that bound is attained.")),
                    Paragraph(Text(
                        "The proof rewrites the difference between the proposed maximum and "
                        + "the profile as ((sqrt(a)-sqrt(b))w-sqrt(b)u)^2 divided by "
                        + "u w (w+u). The denominator is positive, so the square gives the "
                        + "global upper bound. Taking w = sqrt(b)u/(sqrt(a)-sqrt(b)) makes "
                        + "the square vanish and supplies the maximizing witness.")),
                    Paragraph(Text(
                        "This document closes only the one-line optimization lemma in the first "
                        + "part of the source remark. It does not formalize the subsequent zeta "
                        + "zero hypotheses, normalized exclusion curve, or directional "
                        + "Deuring--Heilbronn interpretation."))),
                DescribeRole.Theorem)),
        []));
}
