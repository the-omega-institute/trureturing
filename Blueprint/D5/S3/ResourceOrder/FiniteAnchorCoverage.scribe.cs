using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class FiniteAnchorCoverageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite bounded test families have bounded coverage and admit exact off-union evasion.",
        H("Finite Anchor Coverage"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-anchor-coverage-bound-and-evasion"),
                DeclarationHandle.Create(
                    "D5/S3/ResourceOrder/FiniteAnchorCoverage"
                    + ".finite_anchor_coverage_bound_and_evasion"),
                H("Finite anchor coverage bound and evasion"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("A"), Comma, Sp, F.Id("X"),
                    OpenBracket, Operatorname, Grp(F.Id("Fintype")),
                    Open, F.Id("A"), Close, CloseBracket,
                    OpenBracket, Operatorname, Grp(F.Id("DecidableEq")),
                    Open, F.Id("X"), Close, CloseBracket, Comma, Sp,
                    F.Id("S"), Colon, F.Id("A"), To,
                    Operatorname, Grp(F.Id("Finset")), Open, F.Id("X"), Close,
                    Comma, Sp, F.Id("t"), Colon, F.Id("X"), To,
                    Operatorname, Grp(F.Id("Bool")), Comma, Sp,
                    F.Id("h"), Comma, F.Id("m"), InMacro, Sp,
                    Mathbb, Grp(F.Id("N")), Comma, Sp,
                    Operatorname, Grp(F.Id("card")), Open, F.Id("A"), Close,
                    Leq, D(2), Caret, Grp(F.Id("h")), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("a"), Comma, Sp,
                    Operatorname, Grp(F.Id("card")), Open,
                    F.Id("S"), Open, F.Id("a"), Close, Close,
                    Leq, Sp, F.Id("m"), Close, Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("card")), Open,
                    Operatorname, Grp(F.Id("coveredInputs")), Open,
                    F.Id("S"), Close, Close, Leq,
                    D(2), Caret, Grp(F.Id("h")), Cdot, Sp, F.Id("m"),
                    Sp, Land, Sp,
                    Exists, Sp, F.Id("p"), Colon, F.Id("X"), To,
                    Operatorname, Grp(F.Id("Bool")), Comma, Sp,
                    Open, Forall, Sp, F.Id("a"), Comma, F.Id("x"), Comma, Sp,
                    F.Id("x"), Sp, InMacro, Sp,
                    F.Id("S"), Open, F.Id("a"), Close, Sp, Rightarrow, Sp,
                    F.Id("p"), Open, F.Id("x"), Close, Eq,
                    F.Id("t"), Open, F.Id("x"), Close, Close,
                    Sp, Land, Sp,
                    OpenBrace, F.Id("x"), Sp, Mid, Sp,
                    F.Id("p"), Open, F.Id("x"), Close, Sp, Neq, Sp,
                    F.Id("t"), Open, F.Id("x"), Close, CloseBrace,
                    Eq, F.Id("X"), Sp, Setminus, Sp,
                    Operatorname, Grp(F.Id("coveredInputs")), Open,
                    F.Id("S"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite anchor type represents all possible revealed seeds. The first "
                        + "hypothesis bounds its size by two to the anchor budget, and the second "
                        + "bounds every exposed suite by m inputs. Finset.card_biUnion_le then gives "
                        + "the displayed two-to-h times m coverage bound.")),
                    Paragraph(Text(
                        "The witness implementation agrees with the truth on the union of all "
                        + "possible suites and flips the Boolean truth everywhere else. It therefore "
                        + "passes every suite while its error set is exactly the uncovered complement.")),
                    Paragraph(Text(
                        "This is a partial closure of the leading finite-coverage clause only. The "
                        + "covering-number and logarithmic consequences, the nonatomic-domain clause, "
                        + "and the random-family sufficiency clause remain unresolved.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Finset.card_biUnion_le. Repository searches found no "
                        + "complete theorem combining that bound with the off-union implementation "
                        + "and exact error-set identity."))),
                DescribeRole.Theorem))));
}
