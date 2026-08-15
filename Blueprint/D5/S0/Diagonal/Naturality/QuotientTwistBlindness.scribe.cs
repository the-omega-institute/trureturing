using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Naturality;

internal sealed class QuotientTwistBlindnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A value interface invariant under a twist cannot detect that twist on diagonals.",
        H("Quotient Blindness to Diagonal Twists"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("an-invariant-interface-hides-every-diagonal-twist"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Naturality/QuotientTwistBlindness."
                    + "quotient_twist_blindness"),
                H("An invariant interface hides every diagonal twist"),
                StatementSource.FromAuthor(QuotientTwistBlindnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let A be an address type, Y a value type, Z an observed-value type, "
                            + "q map Y to Z, tau be a self-map of Y, and E be a table indexed "
                            + "twice by A. The twisted diagonal sends a to tau(E(a,a)); the "
                            + "untwisted diagonal sends a to E(a,a).")),
                    Paragraph(Text(
                        "Assume q after tau equals q. Applying q coordinatewise to either "
                            + "diagonal then gives the same observed vector for every table E. "
                            + "Thus exact compatibility at the observed interface need not make "
                            + "the underlying twist visible; no injectivity or surjectivity of q "
                            + "is assumed.")),
                    Paragraph(Text(
                        "Loogle and LeanSearch both returned "
                            + "Function.semiconj_iff_comp_eq for the composition hypothesis. "
                            + "The proof imports and applies the repository's stronger coordinate "
                            + "restriction naturality theorem at the identity address embedding "
                            + "and identity observed twist. Full-statement library and repository "
                            + "searches found no duplicate of this specialization."))),
                DescribeRole.Theorem))));

    private static Formula QuotientTwistBlindnessFormula()
    {
        Formula a = F.Id("A");
        Formula y = F.Id("Y");
        Formula z = F.Id("Z");
        Formula q = F.Id("q");
        Formula tau = F.Id("tau");
        Formula table = F.Id("E");

        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, y, Comma, Sp, z,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Forall, Sp, q, Colon, Sp, new Formula.TypeArrow(y, z), Comma, Sp,
            tau, Colon, Sp, new Formula.TypeArrow(y, y), Comma, Sp,
            table, Colon, Sp, new Formula.TypeArrow(a, new Formula.TypeArrow(a, y)), Comma, Esc,
            Open, q, Sp, Circ, Sp, tau, Sp, Eq, Sp, q, Close,
            Sp, Rightarrow, Sp,
            q, Sp, Circ, Sp, Call("diagonal", tau, table),
            Sp, Eq, Sp,
            q, Sp, Circ, Sp, Call("diagonal", F.Id("id"), table), Dot));
    }
}
