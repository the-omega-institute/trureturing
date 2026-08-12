using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal;

internal sealed class SelfApplicationFatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every non-degenerate binary fractional self-map has exactly one of four fates, with the live fate characterizing the golden family.",
        H("Four Fates of Self-Application"),
        Blocks(
            Paragraph(Text(
                "A binary fractional map is classified as empty, dead, collapsed, or live by "
                + "the coefficients and discriminant of its fixed-point polynomial. For every "
                + "non-degenerate map exactly one classification holds.")),
            Describe.Lean(
                DescribeId.Create("non-degenerate-self-application-has-four-fates"),
                DeclarationHandle.Create("D5/S0/Diagonal/SelfApplicationFates.self_application_four_fates"),
                H("Non-degenerate self-application has exactly one fate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), Comma, Esc,
                    Operatorname, Grp(F.Id("Nondegenerate")), Open, F.Id("m"), Close,
                    Sp, Rightarrow, Sp,
                    Open,
                    Exists, Bang, Sp, F.Id("fate"), Comma, Esc,
                    Operatorname, Grp(F.Id("HasFate")), Open,
                    F.Id("m"), Comma, F.Id("fate"), Close,
                    Close,
                    Sp, Land, Sp,
                    Open,
                    Operatorname, Grp(F.Id("HasFate")), Open,
                    F.Id("m"), Comma, Mathrm, Grp(F.Id("live")), Close,
                    Sp, Leftrightarrow, Sp,
                    Operatorname, Grp(F.Id("IsPhiFamily")), Open, F.Id("m"), Close,
                    Close,
                    Sp, Land, Sp,
                    Open,
                    Operatorname, Grp(F.Id("HasFate")), Open,
                    F.Id("m"), Comma, Mathrm, Grp(F.Id("live")), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("fixedCoefficients")), Open, F.Id("m"), Close,
                    InMacro, OpenBrace,
                    Open, D(1), Comma, Minus, D(1), Comma, Minus, D(1), Close,
                    Comma, Sp,
                    Open, D(1), Comma, D(1), Comma, Minus, D(1), Close,
                    CloseBrace,
                    Close,
                    Sp, Land, Sp,
                    Open,
                    Operatorname, Grp(F.Id("HasFate")), Open,
                    F.Id("m"), Comma, Mathrm, Grp(F.Id("live")), Close,
                    Sp, Rightarrow, Sp,
                    Operatorname, Grp(F.Id("discriminant")), Open, F.Id("m"), Close,
                    Eq, D(1), Caret, D(2), Plus, D(4), Eq, D(5),
                    Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The live cases are precisely the two golden-family maps, whose fixed-point "
                    + "coefficient triples are (1, -1, -1) and (1, 1, -1). In either case the "
                    + "discriminant is 1 squared plus 4, hence exactly 5."))),
                DescribeRole.Theorem))));
}
