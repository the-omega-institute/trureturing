using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase.Interference;

internal sealed class M1728CountershotDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concrete alternating phase walk gives a nonzero residue divisible by twenty-four and forty-eight.",
        H("M1728 Countershot"),
        Blocks(
            Describe.Lean(DescribeId.Create("m1728-countershot"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/M1728Countershot.m1728_countershot"),
                H("The concrete walk is minus forty-eight"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("alternatingWalk")), Open,
                    OpenBracket, D(1), Comma, Sp, D(1), Comma, Sp, D(2, 3), Comma, Sp,
                    D(1), Comma, Sp, D(1), Comma, Sp, D(7, 1), CloseBracket, Close,
                    Sp, Eq, Sp, Minus, D(4, 8), Sp, Land, Sp,
                    Open, Minus, D(4, 8), Close, Sp, Operatorname, Grp(F.Id("mod")),
                    Sp, D(2, 4), Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    Open, Minus, D(4, 8), Close, Sp, Operatorname, Grp(F.Id("mod")),
                    Sp, D(4, 8), Sp, Eq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed address is evaluated directly by the alternating-list definition. "
                            + "The same nonzero result has remainder zero modulo twenty-four and modulo "
                            + "forty-eight. This numerical certificate does not identify the result with a "
                            + "Jacobi selector without a separate address-to-selector bridge."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("m1728-countershot-witness"),
                DeclarationHandle.Create(
                    "D5/S1/Phase/Interference/M1728Countershot.m1728_countershot_witness"),
                H("The countershot has a nonzero witness"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("alternatingWalk")), Open,
                    OpenBracket, D(1), Comma, Sp, D(1), Comma, Sp, D(2, 3), Comma, Sp,
                    D(1), Comma, Sp, D(1), Comma, Sp, D(7, 1), CloseBracket, Close,
                    Sp, Eq, Sp, Minus, D(4, 8), Sp, Land, Sp,
                    Open, Minus, D(4, 8), Close, Neq, Sp, D(0)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concrete address evaluates to minus forty-eight, and the residue is explicitly "
                        + "nonzero, so the divisibility facts above are not a zero-walk artifact."))),
                DescribeRole.Theorem))));
}
