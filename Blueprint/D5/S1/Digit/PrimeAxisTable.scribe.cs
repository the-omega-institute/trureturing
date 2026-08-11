using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class PrimeAxisTableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Finite prime-indexed canonical W digits encode factorization exponents.",
H("Prime-Axis W-Digit Tables"),
Blocks(
            Describe.Lean(
                DescribeId.Create("finite-prime-axis-table-and-product-decode"),
                DeclarationHandle.Create("D5/S1/Digit/PrimeAxisTable.prime_axis_table_spec"),
                H("Finite prime-axis table and product decode"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, F.Id("z"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("PrimeAxisTable")), Comma, Esc, Open, Forall, Sp, F.Id("p"), Comma, Esc, Operatorname, Grp(F.Id("CanonicalRaw")), Open, F.Id("z"), Dot, Operatorname, Grp(F.Id("digits")), Open, F.Id("p"), Close, Close, Close, Sp, Land, Sp, Operatorname, Grp(F.Id("Finite")), Open, Operatorname, Grp(F.Id("support")), Open, F.Id("z"), Dot, Operatorname, Grp(F.Id("digits")), Close, Close, Sp, Land, Sp, Open, Forall, Sp, F.Id("p"), Comma, Esc, Operatorname, Grp(F.Id("axisExponent")), Open, F.Id("z"), Comma, F.Id("p"), Close, Sp, Eq, Sp, Sum, Underscore, Grp(F.Id("k"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("support")), Open, F.Id("z"), Dot, Operatorname, Grp(F.Id("digits")), Open, F.Id("p"), Close, Close), Sp, F.Id("z"), Dot, Operatorname, Grp(F.Id("digits")), Open, F.Id("p"), Comma, F.Id("k"), Close, Thin, F.Id("w"), Open, F.Id("k"), Close, Close, Sp, Land, Sp, Operatorname, Grp(F.Id("decodePrimeAxisTable")), Open, F.Id("z"), Close, Sp, Eq, Sp, Prod, Underscore, Grp(F.Id("p"), Sp, InMacro, Sp, Operatorname, Grp(F.Id("support")), Open, F.Id("z"), Dot, Operatorname, Grp(F.Id("digits")), Close), Sp, F.Id("p"), Caret, Grp(Operatorname, Grp(F.Id("axisExponent")), Open, F.Id("z"), Comma, F.Id("p"), Close)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An outer finitely supported table assigns canonical binary nonadjacent W digits to prime axes. The theorem exposes finite global support, each W-weighted exponent sum, and the corresponding finite prime-power product decode."))),
                DescribeRole.Theorem))));
}
