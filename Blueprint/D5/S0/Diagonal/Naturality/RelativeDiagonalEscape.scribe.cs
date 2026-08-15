using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Naturality;

internal sealed class RelativeDiagonalEscapeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-point-free twist sends every diagonal listing outside its range.",
        H("Relative Diagonal Escape"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a-fixed-point-free-twist-escapes-every-listing"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Naturality/RelativeDiagonalEscape."
                    + "relative_diagonal_escape"),
                H("A fixed-point-free twist escapes every listing"),
                StatementSource.FromAuthor(RelativeDiagonalEscapeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A be an address type, Y a value type, e a table indexed twice by A, "
                            + "and tau a self-map of Y. The twisted diagonal sends each address a "
                            + "to tau(e(a,a)).")),
                    Paragraph(Text(
                        "Assume tau has no fixed point. If the twisted diagonal were a row e(a), "
                            + "then evaluating that row equality at a would make e(a,a) a fixed "
                            + "point of tau. Therefore the twisted diagonal is outside the range "
                            + "of e, without finiteness assumptions on either type.")),
                    Paragraph(Text(
                        "Loogle found Function.exists_fixed_point_of_surjective as a related "
                            + "surjectivity theorem, while LeanSearch and pinned-Mathlib searches "
                            + "found no full-statement match. The proof imports and applies the "
                            + "repository lemma EscapeCount.diagonal_landing_fixed."))),
                DescribeRole.Theorem))));

    private static Formula RelativeDiagonalEscapeFormula()
    {
        Formula a = F.Id("A");
        Formula y = F.Id("Y");
        Formula listing = F.Id("e");
        Formula tau = F.Id("tau");
        Formula value = F.Id("y");

        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, y,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Forall, Sp, listing, Colon, Sp,
            new Formula.TypeArrow(a, new Formula.TypeArrow(a, y)), Comma, Sp,
            tau, Colon, Sp, new Formula.TypeArrow(y, y), Comma, Esc,
            Open, Forall, Sp, value, Colon, Sp, y, Comma, Sp,
            Call("tau", value), Sp, Neq, Sp, value, Close,
            Sp, Rightarrow, Sp,
            Neg, Sp, Open,
            Call("diagonal", tau, listing),
            Sp, InMacro, Sp,
            Operatorname, Grp(F.Id("range")), Open, listing, Close,
            Close, Dot));
    }
}
