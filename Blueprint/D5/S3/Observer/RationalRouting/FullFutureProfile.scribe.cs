using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.RationalRouting;

internal sealed class FullFutureProfileDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/RationalRouting/FullFutureProfile.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A bounded vector of instantaneous floors determines every finite future word and has an exact finite cell evaluator.",
        H("Finite cells for complete future profiles"),
        Blocks(
            Paragraph(Text("The carrier is every positive rational, with no denominator bound. False acts by L(x)=x/(1+x), true by R(x)=x+1, and the head of a word acts first. A reply at any positive integer scale m is the entire integer floor of m times the current value. SameInstant at B compares all scales 1 through B, including noncoprime scales; SameFuture quantifies over every finite chronological word, including the empty word. A predicted word is an index of a calculation, not an executed experiment.")),
            Describe.Lean(DescribeId.Create("instantaneous-vector-is-the-full-future-profile"),
                DeclarationHandle.Create(Prefix + "instantaneous_iff_full_future"),
                H("All future words from a finite vector"),
                StatementSource.FromAuthor(InstantStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a left action, a threshold j at scale m pulls back to the comparison with j/(m-j), whose positive denominator is at most m. Every such comparison is already determined by the original vector. A right action adds the integer m to its scale-m report. Induction through an arbitrary finite word therefore preserves the whole vector. The reverse implication uses the empty word."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("containing-cell-exact-class"),
                DeclarationHandle.Create(Prefix + "containing_cell_exact"),
                H("The exact containing cell"),
                StatementSource.FromAuthor(CellStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a positive representative y, the lower endpoint is the maximum of zero and floor(sy)/s over original denominators 1 through B. The upper endpoint is the minimum of (floor(sy)+1)/s. The lower endpoint is included when positive; zero is excluded by positivity. The upper endpoint is always excluded. Thus membership is exactly equality of all instantaneous replies and, by the preceding theorem, equality of the complete future profile. The unreduced grids have the same positive cuts as the reduced fractions with denominator at most B. Integer cuts make every upper endpoint finite, including the first cell (0,1/B)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-cell-universal-evaluator"),
                DeclarationHandle.Create(Prefix + "containing_cell_evaluator"),
                H("Finite evaluation of every coordinate"),
                StatementSource.FromAuthor(EvaluatorStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the formula C denotes containingCell(B,y). Choose the included lower endpoint if it is positive, or half the upper endpoint in the zero slice. This rational belongs to the cell. Exact arithmetic along any supplied finite word followed by one floor computes its coordinate for every possible original in the cell. The word length and requested scale are arbitrary finite inputs; an infinite tuple is never stored or emitted."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("unreduced-endpoint-scan-computes-the-cell"),
                DeclarationHandle.Create(Prefix + "fast_containing_cell_eq"),
                H("Selecting endpoints without reductions in the scan"),
                StatementSource.FromAuthor(FastStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The executable endpoint scan uses integer quotients and cross-product comparisons. The executable pass is tail recursive; its state is the current denominator and the selected lower and upper numerator-denominator pairs. An exact refinement proof identifies its output with the recursive grid-intersection specification. Reduction takes place when those final two pairs become rational endpoints. Its projection agrees exactly with the mathematical cell intersection, so the moving-cut acquisition can use this representation without changing the output cell."))),
                DescribeRole.Theorem))));

    private static Formula App(string name, params Formula[] arguments) =>
        F.Seq(F.Operatorname, F.Sp, F.Grp(F.Id(name)), F.Open, F.Seq(arguments), F.Close);

    private static Formula Let(string name, Formula type, Formula value) =>
        F.Seq(F.Operatorname, F.Sp, F.Grp(F.Id("let")), F.Sp, F.Id(name), F.Colon, F.Sp,
            type, F.Eq, value, F.Semi, F.Sp);

    private static Formula InstantStatement() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("B"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("N")), F.Comma,
        F.Id("x"), F.Comma, F.Id("y"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Q")), F.Comma,
        F.D(0), F.Lt, F.Id("x"), F.Land, F.Sp, F.D(0), F.Lt, F.Id("y"), F.Longrightarrow, F.Sp,
        F.Open, App("SameInstant", F.Id("B"), F.Comma, F.Id("x"), F.Comma, F.Id("y")), F.Iff, F.Sp,
        App("SameFuture", F.Id("B"), F.Comma, F.Id("x"), F.Comma, F.Id("y")), F.Close));

    private static Formula CellStatement() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("B"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("N")), F.Comma,
        F.Id("x"), F.Comma, F.Id("y"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Q")), F.Comma,
        F.D(1), F.Le, F.Sp, F.Id("B"), F.Land, F.Sp, F.D(0), F.Lt, F.Id("y"), F.Longrightarrow, F.Sp,
        F.Open, App("Contains", App("containingCell", F.Id("B"), F.Comma, F.Id("y")), F.Comma, F.Id("x")),
        F.Iff, F.Sp, F.D(0), F.Lt, F.Id("x"), F.Land, F.Sp,
        App("SameInstant", F.Id("B"), F.Comma, F.Id("x"), F.Comma, F.Id("y")), F.Close));

    private static Formula EvaluatorStatement() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("B"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("N")), F.Comma,
        F.Id("y"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Q")), F.Comma,
        F.D(1), F.Le, F.Sp, F.Id("B"), F.Land, F.Sp, F.D(0), F.Lt, F.Id("y"), F.Longrightarrow, F.Sp,
        Let("C", App("ProfileCell"), App("containingCell", F.Id("B"), F.Comma, F.Id("y"))),
        F.Open, App("Contains", F.Id("C"), F.Comma, App("representative", F.Id("C"))), F.Land, F.Sp,
        F.Open, F.Forall, F.Sp, F.Id("x"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Q")), F.Comma,
        App("Contains", F.Id("C"), F.Comma, F.Id("x")), F.Longrightarrow, F.Sp,
        F.Forall, F.Sp, F.Id("w"), F.InMacro, F.Sp, App("List", App("Bool")), F.Comma,
        F.Id("m"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("N")), F.Comma,
        F.D(1), F.Le, F.Sp, F.Id("m"), F.Le, F.Sp, F.Id("B"), F.Longrightarrow, F.Sp,
        App("evaluate", F.Id("C"), F.Comma, F.Id("w"), F.Comma, F.Id("m")), F.Eq,
        App("reply", F.Id("m"), F.Comma, App("attain", F.Id("w"), F.Comma, F.Id("x"))), F.Close, F.Close));

    private static Formula FastStatement() => F.Disp(F.Seq(
        F.Forall, F.Sp, F.Id("B"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("N")), F.Comma,
        F.Id("y"), F.InMacro, F.Sp, F.Mathbb, F.Sp, F.Grp(F.Id("Q")), F.Comma,
        App("fastContainingCell", F.Id("B"), F.Comma, F.Id("y")), F.Eq,
        App("containingCell", F.Id("B"), F.Comma, F.Id("y"))));
}
