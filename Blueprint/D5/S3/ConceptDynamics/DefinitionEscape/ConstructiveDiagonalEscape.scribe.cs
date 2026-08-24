using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class ConstructiveDiagonalEscapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical twisted diagonal escapes every supplied catalog.",
        H("Constructive Diagonal Escape"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("constructive-diagonal-escape"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/ConstructiveDiagonalEscape."
                        + "constructive_diagonal_escape"),
                H("The canonical diagonal escapes its catalog"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The address type, value type, catalog, and twist are independent source "
                            + "primitives. The escaped function is the established canonical "
                            + "diagonal, sending a to the twist of g(a)(a).")),
                    Paragraph(Text(
                        "When the twist has no fixed point, this diagonal cannot equal any catalog "
                            + "row. Equality with row g(a) would make g(a)(a) a fixed point after "
                            + "evaluation at a.")),
                    Paragraph(Text(
                        "The repository contains the exact arbitrary-carrier range theorem, so the "
                            + "Lean proof imports and applies it directly. Pinned Mathlib has related "
                            + "surjectivity and Cantor results but no thinner full-statement match."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula address = F.Id("A");
        Formula valueType = F.Id("Y");
        Formula catalog = F.Id("g");
        Formula twist = F.Id("tau");
        Formula value = F.Id("y");
        Formula diagonal = Call("diagonal", twist, catalog);

        return Disp(Seq(
            Forall, Sp, address, Comma, Sp, valueType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            catalog, Colon, Sp,
            new Formula.TypeArrow(address, new Formula.TypeArrow(address, valueType)),
            Comma, Sp, twist, Colon, Sp,
            new Formula.TypeArrow(valueType, valueType), Comma, RowBreak, Grp(),
            Open, Forall, Sp, value, Colon, Sp, valueType, Comma, Sp,
            Call("tau", value), Sp, Neq, Sp, value, Close,
            Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Open, diagonal, Sp, InMacro, Sp,
            Call("range", catalog), Close, Dot));
    }
}
