using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Conventions;

internal sealed class TotalCodeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S0/Conventions/TotalCode",
                "Total-code-preserving transformations cannot hide object changes."),
            H("No Invisible Register"),
            Blocks(
                DocumentBlock.Describe.Theorem(
                    DescribeId.Create("no-hidden-register"),
                    H("Preserving the total code preserves the object"),
                    LeanTheorem("D5/S0/Conventions/TotalCode.no_hidden_register"),
                    Disp(Seq(Forall, Sp, F.Id("D"), Comma, F.Id("R"), Comma, F.Id("L"), Comma, Quad, Sp, Left, OpenBracket, Forall, Sp, F.Id("f"), Colon, Operatorname, Grp(F.Id("TotalCode")), Open, F.Id("D"), Comma, F.Id("R"), Comma, F.Id("L"), Close, To, Operatorname, Grp(F.Id("TotalCode")), Open, F.Id("D"), Comma, F.Id("R"), Comma, F.Id("L"), Close, Comma, Esc, Left, Open, Forall, Sp, F.Id("X"), Comma, Esc, Operatorname, Grp(F.Id("data")), Open, F.Id("f"), Open, F.Id("X"), Close, Close, Eq, Operatorname, Grp(F.Id("data")), Open, F.Id("X"), Close, Right, Close, Land, Sp, Left, Open, Forall, Sp, F.Id("X"), Comma, Esc, Operatorname, Grp(F.Id("rules")), Open, F.Id("f"), Open, F.Id("X"), Close, Close, Eq, Operatorname, Grp(F.Id("rules")), Open, F.Id("X"), Close, Right, Close, Land, Sp, Left, Open, Forall, Sp, F.Id("X"), Comma, Esc, Operatorname, Grp(F.Id("ledger")), Open, F.Id("f"), Open, F.Id("X"), Close, Close, Eq, Operatorname, Grp(F.Id("ledger")), Open, F.Id("X"), Close, Right, Close, Rightarrow, Forall, Sp, F.Id("X"), Comma, Esc, F.Id("f"), Open, F.Id("X"), Close, Eq, F.Id("X"), Right, CloseBracket, Land, Sp, Left, OpenBracket, Forall, Sp, F.Id("f"), Comma, F.Id("X"), Comma, Esc, F.Id("f"), Open, F.Id("X"), Close, Neq, Sp, F.Id("X"), Rightarrow, Sp, Operatorname, Grp(F.Id("data")), Open, F.Id("f"), Open, F.Id("X"), Close, Close, Neq, Operatorname, Grp(F.Id("data")), Open, F.Id("X"), Close, Lor, Sp, Operatorname, Grp(F.Id("rules")), Open, F.Id("f"), Open, F.Id("X"), Close, Close, Neq, Operatorname, Grp(F.Id("rules")), Open, F.Id("X"), Close, Lor, Sp, Operatorname, Grp(F.Id("ledger")), Open, F.Id("f"), Open, F.Id("X"), Close, Close, Neq, Operatorname, Grp(F.Id("ledger")), Open, F.Id("X"), Close, Right, CloseBracket, Dot)),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "The semantic kernel-identity criterion is represented here by "
                        + "Lean structure equality, not claimed as a proof of an ontological "
                        + "identity criterion. Extensionality proves both the preservation "
                        + "clause and its componentwise dual. This is the C3a identity pillar "
                        + "announced for use in 23.4.")))))));
}
