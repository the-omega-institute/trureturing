using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Mechanical;

internal sealed class GoldenFiberPrefixCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive-indexed golden fiber letters have an exact floor prefix count.",
        H("Golden Fiber Prefix Count"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-indexed-golden-fiber-letter"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/GoldenFiberPrefixCount.goldenFiberLetter"),
                H("Positive-indexed golden fiber letter"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    F.Id("f"), Underscore, F.Id("m"), Sp, Eq, Sp, D(1), Sp, Plus, Sp,
                    Mathbf, Grp(D(1)), Underscore, Grp(
                        Operatorname, Grp(F.Id("goldenWord")), Open,
                        F.Id("m"), Minus, D(1), Close, Eq, Mathrm, Grp(F.Id("true")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a natural index m, the fiber letter is one plus the indicator of the "
                    + "golden-word bit at m minus one. Thus its positive-index sequence begins "
                    + "2, 1, 2, 2, 1, and agrees with the established one-index mechanical "
                    + "bridge."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("golden-fiber-positive-prefix-count"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Mechanical/GoldenFiberPrefixCount.golden_fiber_prefix_count"),
                H("Golden fiber prefixes have the exact floor count"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("n"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Sum, Underscore, Grp(F.Id("m"), Eq, D(1)), Caret, Grp(F.Id("n")), Sp,
                    F.Id("f"), Underscore, F.Id("m"), Sp, Eq, Sp,
                    Lfloor, Varphi, Open, F.Id("n"), Plus, D(1), Close, Rfloor,
                    Sp, Minus, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n, summing the positive-indexed letters f_m from "
                        + "m = 1 through n gives floor(phi times (n + 1)) minus one. The empty "
                        + "prefix at n = 0 is included.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. Its golden-ratio inverse "
                        + "and conjugate identities and its integer-floor shift laws are exact "
                        + "component hits, but no declaration states this prefix identity. The "
                        + "repository search likewise found no duplicate. GoldenBeattyCount proves "
                        + "the closely related inverse threshold including index zero, but does not "
                        + "state this positive-fiber sum. The direct reusable hits are the generic "
                        + "lowerMechanicalWindowTrueCount_eq_floor theorem and the exact golden-word "
                        + "shift lowerMechanicalWord_golden, so this declaration is a thin "
                        + "specialization: count the true bits in the shifted mechanical window, "
                        + "then rewrite phi as one plus its inverse.")),
                    Paragraph(Text(
                        "This is an honest partial closure of clause (i) only. The later constant "
                        + "evaluation, limit formulas, isolated correction term, zero-drift claim, "
                        + "and numerical registration in clauses (ii) through (v) remain unresolved "
                        + "and are not asserted here."))),
                DescribeRole.Theorem))));
}
