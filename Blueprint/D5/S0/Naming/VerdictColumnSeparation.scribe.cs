using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming;

internal sealed class VerdictColumnSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extending an implementation population can separate verdict columns that previously agreed.",
        H("Verdict Column Separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("verdict-columns-can-split"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/VerdictColumnSeparation.verdict_columns_can_split"),
                H("A new implementation can split two previously identical verdict columns"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("I"), Comma, Sp, F.Id("T"), Comma, Sp, F.Id("V"), Comma, Sp,
                    F.Id("r"), Colon, Sp, F.Id("I"), Sp, To, Sp, F.Id("T"), Sp, To, Sp, F.Id("V"),
                    Comma, Sp, F.Id("t1"), Comma, Sp, F.Id("t2"), Comma, Sp,
                    Open, Operatorname, Grp(F.Id("Nontrivial")), Open, F.Id("V"), Close,
                    Sp, Land, Sp,
                    F.Id("t1"), Sp, Neq, Sp, F.Id("t2"), Sp, Land, Sp,
                    Forall, Sp, F.Id("i"), Comma, Sp,
                    F.Id("r"), Open, F.Id("i"), Comma, Sp, F.Id("t1"), Close, Sp, Eq, Sp,
                    F.Id("r"), Open, F.Id("i"), Comma, Sp, F.Id("t2"), Close, Close,
                    Sp, Rightarrow, Sp, Exists, Sp, Widehat, Grp(F.Id("r")), Comma, Sp,
                    Widehat, Grp(F.Id("r")), Colon, Sp,
                    Operatorname, Grp(F.Id("Option")), Open, F.Id("I"), Close,
                    Sp, To, Sp, F.Id("T"), Sp, To, Sp, F.Id("V"), Comma, Sp,
                    Open, Forall, Sp, F.Id("i"), Comma, Sp, F.Id("t"), Comma, Sp,
                    Widehat, Grp(F.Id("r")), Open,
                    Operatorname, Grp(F.Id("some")), Open, F.Id("i"), Close, Comma, Sp,
                    F.Id("t"), Close, Sp, Eq, Sp,
                    F.Id("r"), Open, F.Id("i"), Comma, Sp, F.Id("t"), Close, Close,
                    Sp, Land, Sp,
                    Widehat, Grp(F.Id("r")), Open,
                    Operatorname, Grp(F.Id("none")), Comma, Sp, F.Id("t1"), Close, Sp, Neq, Sp,
                    Widehat, Grp(F.Id("r")), Open,
                    Operatorname, Grp(F.Id("none")), Comma, Sp, F.Id("t2"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let r pair an arbitrary implementation population with an arbitrary test "
                        + "space and take values in a verdict type containing at least two distinct "
                        + "values. Suppose two distinct tests have identical verdict columns on every "
                        + "current implementation. After adjoining one implementation, r extends "
                        + "without changing any old verdict, while the new implementation assigns "
                        + "different verdicts to the two tests.")),
                    Paragraph(Text(
                        "The construction uses the option type for the enlarged population. Existing "
                        + "implementations retain their original verdict rows; the new point receives "
                        + "one of two distinct verdicts according to whether the test is the first "
                        + "distinguished test.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched for equal or identical columns, column splitting, "
                        + "population extension, and adjoining a point; no exact theorem was found. "
                        + "Function extension and option-recursion infrastructure were found, and the "
                        + "Lean proof gives the direct option extension.")),
                    Paragraph(Text(
                        "This is an honest partial closure of clause (c) only. The double extensional "
                        + "quotient claim, the minimization characterization, and the engineering-history "
                        + "discussion carried by the source atom remain unresolved."))),
                DescribeRole.Theorem)),
        []));
}
