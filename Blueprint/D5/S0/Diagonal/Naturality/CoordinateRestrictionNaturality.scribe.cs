using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Naturality;

internal sealed class CoordinateRestrictionNaturalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate restriction preserves twisted diagonals for compatible value maps.",
        H("Coordinate Restriction Naturality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coordinate-restriction-commutes-with-twisted-diagonalization"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Naturality/CoordinateRestrictionNaturality."
                    + "coordinate_restriction_naturality"),
                H("Coordinate restriction commutes with twisted diagonalization"),
                StatementSource.FromAuthor(CoordinateRestrictionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Ai and Aj be address types, Yi and Yj be value types, iota embed "
                        + "Ai into Aj, and q map Yj to Yi. Restrict a table E by sending (a,b) "
                        + "to q(E(iota(a),iota(b))), and restrict a vector u by sending a to "
                        + "q(u(iota(a))).")),
                    Paragraph(Text(
                        "For twists tauJ on Yj and tauI on Yi, assume q after tauJ equals "
                        + "tauI after q. Then restricting the tauJ-twisted diagonal of every "
                        + "table E equals the tauI-twisted diagonal of the restricted table. "
                        + "The proof evaluates the imported semiconjugacy equivalence at each "
                        + "diagonal entry.")),
                    Paragraph(Text(
                        "Loogle and LeanSearch found Function.semiconj_iff_comp_eq for the exact "
                        + "intertwining hypothesis, and the Lean proof imports and applies it. "
                        + "Neither search found the full coordinate-restriction statement; "
                        + "repository and digestion-record searches found no duplicate."))),
                DescribeRole.Theorem))));

    private static Formula CoordinateRestrictionFormula()
    {
        Formula ai = Seq(F.Id("A"), Underscore, Grp(F.Id("i")));
        Formula aj = Seq(F.Id("A"), Underscore, Grp(F.Id("j")));
        Formula yi = Seq(F.Id("Y"), Underscore, Grp(F.Id("i")));
        Formula yj = Seq(F.Id("Y"), Underscore, Grp(F.Id("j")));
        Formula iota = F.Id("iota");
        Formula q = F.Id("q");
        Formula tauI = Seq(F.Id("tau"), Underscore, Grp(F.Id("i")));
        Formula tauJ = Seq(F.Id("tau"), Underscore, Grp(F.Id("j")));
        Formula table = F.Id("E");

        return Disp(Seq(
            Forall, Sp, ai, Comma, Sp, aj, Comma, Sp, yi, Comma, Sp, yj,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Forall, Sp, iota, Colon, Sp, Call("Embedding", ai, aj), Comma, Sp,
            q, Colon, Sp, new Formula.TypeArrow(yj, yi), Comma, Esc,
            tauJ, Colon, Sp, new Formula.TypeArrow(yj, yj), Comma, Sp,
            tauI, Colon, Sp, new Formula.TypeArrow(yi, yi), Comma, Esc,
            table, Colon, Sp,
            new Formula.TypeArrow(aj, new Formula.TypeArrow(aj, yj)), Comma, Esc,
            Open, q, Sp, Circ, Sp, tauJ, Sp, Eq, Sp, tauI, Sp, Circ, Sp, q, Close,
            Sp, Rightarrow, Sp,
            Call("restrictVector", iota, q, Call("diagonal", tauJ, table)),
            Sp, Eq, Sp,
            Call("diagonal", tauI, Call("restrictTable", iota, q, table)), Dot));
    }
}
