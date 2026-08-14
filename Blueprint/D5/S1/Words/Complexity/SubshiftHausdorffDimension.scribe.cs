using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity;

internal sealed class SubshiftHausdorffDimensionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial factor complexity forces the associated prefix-language subshift to have Hausdorff dimension zero.",
        H("Polynomial Complexity and Subshift Hausdorff Dimension"),
        Blocks(
            Paragraph(Text(
                "Let x be a one-sided infinite word over a finite nontrivial discrete alphabet. "
                + "Its prefix-language subshift consists of the infinite words whose prefix of "
                + "every length occurs somewhere as a factor of x.")),
            Describe.Lean(
                DescribeId.Create("prefix-language-subshift"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/SubshiftHausdorffDimension.wordSubshift"),
                H("The subshift is defined by the factor language of the base word"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("X"), Underscore, F.Id("x"), Sp, Eq, Sp, OpenBrace,
                    F.Id("y"), Sp, Colon, Sp, Forall, Sp, F.Id("n"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp, F.Id("P"), Underscore,
                    F.Id("n"), Open, F.Id("y"), Close, InMacro, Sp, F.Id("F"),
                    Underscore, F.Id("x"), Open, F.Id("n"), Close, CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The factor set uses natural starting positions and represents a length-n word "
                    + "as a function on Fin n. No two-sided extension is built into this definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("base-word-in-subshift"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/SubshiftHausdorffDimension."
                        + "self_mem_wordSubshift"),
                H("The base word belongs to its subshift"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("x"), InMacro, Sp, F.Id("X"), Underscore, F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every prefix of x occurs at starting position zero, so the defining language "
                    + "condition holds at every length."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-step-shift-invariance"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/SubshiftHausdorffDimension."
                        + "wordSubshift_shift_invariant"),
                H("The subshift is invariant under the one-step shift"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("y"), InMacro, Sp, F.Id("X"), Underscore, F.Id("x"), Sp,
                    Rightarrow, Sp, F.Id("s"), Open, F.Id("y"), Close, InMacro, Sp,
                    F.Id("X"), Underscore, F.Id("x")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A shifted prefix of length n is obtained by deleting the first letter from "
                    + "a length-(n+1) prefix. Its occurrence therefore moves one natural position "
                    + "to the right inside the base word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polynomial-complexity-zero-hausdorff-measure"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/SubshiftHausdorffDimension."
                        + "hausdorffMeasure_wordSubshift_eq_zero"),
                H("Positive-dimensional Hausdorff measures vanish"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Sp, Operatorname, Grp(F.Id("card")), Open, F.Id("F"),
                    Underscore, F.Id("x"), Open, F.Id("n"), Close, Close, Sp, Leq, Sp,
                    F.Id("C"), Sp, Times, Sp, Open, F.Id("n"), Plus, D(1), Close,
                    Caret, Grp(F.Id("k")),
                    Close, Sp, Land, Sp, D(0), Sp, Lt, Sp, F.Id("d"), Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("muH")), Open, F.Id("d"), Comma, Sp,
                    F.Id("X"), Underscore, F.Id("x"), Close, Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At depth n, the allowed factors index a finite cover by prefix cylinders. "
                        + "Each cylinder has extended diameter at most 2^(-n), while the number of "
                        + "cylinders is bounded by C(n+1)^k.")),
                    Paragraph(Text(
                        "For every d > 0, polynomial growth times the exponential factor "
                        + "((1/2)^d)^n tends to zero. Mathlib's finite-cover liminf estimate then "
                        + "forces the d-dimensional Hausdorff measure to vanish."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("polynomial-complexity-zero-dimension"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/SubshiftHausdorffDimension."
                        + "dimH_wordSubshift_eq_zero"),
                H("Polynomial-complexity subshifts have dimension zero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("n"), InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Sp, Operatorname, Grp(F.Id("card")), Open, F.Id("F"),
                    Underscore, F.Id("x"), Open, F.Id("n"), Close, Close, Sp, Leq, Sp,
                    F.Id("C"), Sp, Times, Sp, Open, F.Id("n"), Plus, D(1), Close,
                    Caret, Grp(F.Id("k")),
                    Close, Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("dimH")), Open,
                    F.Id("X"), Underscore, F.Id("x"), Close, Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Vanishing at every positive exponent places the Hausdorff dimension below "
                    + "every positive nonnegative real. Nonnegativity supplies the reverse bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-subshift-zero-dimension"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Complexity/SubshiftHausdorffDimension."
                        + "dimH_goldenSubshift_eq_zero"),
                H("The golden subshift has dimension zero"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("dimH")), Open, F.Id("X"), Underscore,
                    F.Id("g"), Close, Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The exact golden factor count is n+1. The formal bridge maps each "
                        + "Fin-indexed factor to its list representation with List.ofFn and uses "
                        + "injectivity to preserve finite-set cardinality.")),
                    Paragraph(Text(
                        "This document does not identify the prefix-language set with an orbit "
                        + "closure, and it does not establish closedness, uncountability, or "
                        + "perfectness."))),
                DescribeRole.Theorem))));
}
