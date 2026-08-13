using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class DedekindFamilySplitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The oriented Dedekind ledger splits into its alternating walk and endpoint translation.",
        H("Dedekind Family Split"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dedekind-family-split"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/DedekindFamilySplit.dedekind_family_split"),
                H("The oriented ledger splits into walk and translation"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("a"), InMacro, Sp, Operatorname,
                    Grp(F.Id("List")), Open, Mathbb, Grp(F.Id("Z")), Close, Comma, Esc,
                    Forall, Sp, F.Id("phi"), Comma, Sp, F.Id("psi"), InMacro, Sp,
                    Mathbb, Grp(F.Id("Q")), Comma, Esc,
                    Forall, Sp, F.Id("u"), Comma, Sp, F.Id("v"), Comma, Sp,
                    F.Id("c"), Comma, Sp, F.Id("t"), InMacro, Sp,
                    Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    F.Id("c"), Neq, Sp, D(0), Comma, Sp,
                    F.Id("phi"), Eq, D(3), Plus,
                    OpenBracket, Operatorname, Grp(F.Id("alt")), Open, F.Id("a"), Close,
                    CloseBracket, Underscore, Grp(Mathbb, Grp(F.Id("Q"))), Plus,
                    Frac,
                    Grp(OpenBracket, F.Id("u"), Minus, F.Id("v"), CloseBracket,
                        Underscore, Grp(Mathbb, Grp(F.Id("Q")))),
                    Grp(OpenBracket, F.Id("c"), CloseBracket,
                        Underscore, Grp(Mathbb, Grp(F.Id("Q")))), Comma, Sp,
                    F.Id("psi"), Eq, F.Id("phi"), Minus, D(3), Comma, Sp,
                    F.Id("u"), Minus, F.Id("v"), Eq, F.Id("c"), F.Id("t"), Sp,
                    Rightarrow, Sp,
                    F.Id("psi"), Eq,
                    OpenBracket, Operatorname, Grp(F.Id("alt")), Open, F.Id("a"), Close,
                    CloseBracket, Underscore, Grp(Mathbb, Grp(F.Id("Q"))), Plus,
                    OpenBracket, F.Id("t"), CloseBracket, Underscore,
                    Grp(Mathbb, Grp(F.Id("Q"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here alt(a) is the alternating integer walk of the coefficient list. " +
                        "The endpoint hypothesis identifies the rational correction with the " +
                        "integer translation, and psi = phi - 3 removes the constant term.")),
                    Paragraph(Text(
                        "This is a deeper-clause continuation for the oriented family-split " +
                        "identity only; the empirical enumeration and asymptotic clauses remain open."))),
                DescribeRole.Theorem)),
        []));
}
