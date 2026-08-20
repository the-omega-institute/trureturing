using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.DivergenceSupport.Equality;

internal sealed class PetzClassicalCorollaryDocument : IScribeDocumentDefinition
{
    private const string LeanDeclaration =
        "D5/S3/DivergenceSupport/Equality/PetzClassicalCorollary."
            + "zero_defect_equivalences_and_permutation_channel";

    private static Formula Output(Formula channel, Formula law) =>
        F.Seq(F.Open, channel, law, F.Close);

    private static Formula OutputAt(Formula channel, Formula law, Formula y) =>
        F.Seq(Output(channel, law), F.Open, y, F.Close);

    private static Formula Posterior(Formula law, Formula y) => F.Seq(
        F.Widehat, F.Grp(law), F.Underscore, F.Grp(y));

    private static Formula Divergence(Formula left, Formula right) => F.Seq(
        F.Id("D"), F.Open, left, F.Vert, F.Vert, F.Sp, right, F.Close);

    private static Formula Defect(Formula channel) => F.Seq(
        Divergence(F.Id("p"), F.Id("q")), F.Sp, F.Minus, F.Sp,
        Divergence(Output(channel, F.Id("p")), Output(channel, F.Id("q"))));

    private static Formula Statement()
    {
        var x = F.Id("x");
        var y = F.Id("y");
        var p = F.Id("p");
        var q = F.Id("q");
        var w = F.Id("W");
        var r = F.Id("R");
        var e = F.Id("e");
        var pe = F.Seq(F.Id("P"), F.Underscore, F.Grp(e));
        var wpAtY = OutputAt(w, p, y);
        var wqAtY = OutputAt(w, q, y);

        return F.Disp(F.Seq(
            F.Begin, F.Grp(F.Id("gathered")),
            F.Forall, F.Sp, F.Id("X"), F.Comma, F.Sp, F.Id("Y"), F.Esc,
            F.OpenBracket, F.Operatorname, F.Grp(F.Id("Fintype")),
            F.Open, F.Id("X"), F.Close, F.CloseBracket, F.Sp,
            F.OpenBracket, F.Operatorname, F.Grp(F.Id("Fintype")),
            F.Open, F.Id("Y"), F.Close, F.CloseBracket, F.Comma, F.RowBreak,
            F.Forall, F.Sp, p, F.Comma, F.Sp, q, F.Colon, F.Sp,
            F.Id("X"), F.To, F.Sp, F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.Sp,
            w, F.Colon, F.Sp, F.Id("X"), F.To, F.Sp, F.Id("Y"), F.To, F.Sp,
            F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.RowBreak,
            F.Open, F.Open, F.Forall, F.Sp, x, F.Colon, F.Sp, F.Id("X"), F.Comma,
            F.Sp, F.D(0), F.Le, F.Sp, p, F.Open, x, F.Close, F.Close,
            F.Sp, F.Land, F.Sp, F.Sum, F.Underscore, F.Grp(x), p,
            F.Open, x, F.Close, F.Sp, F.Eq, F.Sp, F.D(1), F.Close,
            F.Sp, F.Rightarrow, F.RowBreak,
            F.Open, F.Open, F.Forall, F.Sp, x, F.Colon, F.Sp, F.Id("X"), F.Comma,
            F.Sp, F.D(0), F.Le, F.Sp, q, F.Open, x, F.Close, F.Close,
            F.Sp, F.Land, F.Sp, F.Sum, F.Underscore, F.Grp(x), q,
            F.Open, x, F.Close, F.Sp, F.Eq, F.Sp, F.D(1), F.Close,
            F.Sp, F.Rightarrow, F.RowBreak,
            F.Open, F.Forall, F.Sp, x, F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
            q, F.Open, x, F.Close, F.Sp, F.Eq, F.Sp, F.D(0), F.Sp,
            F.Rightarrow, F.Sp, p, F.Open, x, F.Close,
            F.Sp, F.Eq, F.Sp, F.D(0), F.Close, F.Sp, F.Rightarrow, F.RowBreak,
            F.Open, F.Open, F.Forall, F.Sp, x, F.Colon, F.Sp, F.Id("X"), F.Comma,
            F.Sp, y, F.Colon, F.Sp, F.Id("Y"), F.Comma, F.Sp, F.D(0), F.Le, F.Sp,
            w, F.Open, x, F.Comma, F.Sp, y, F.Close, F.Close, F.Sp, F.Land, F.Sp,
            F.Open, F.Forall, F.Sp, x, F.Colon, F.Sp, F.Id("X"), F.Comma, F.Sp,
            F.Sum, F.Underscore, F.Grp(y), w, F.Open, x, F.Comma, F.Sp, y, F.Close,
            F.Sp, F.Eq, F.Sp, F.D(1), F.Close, F.Close,
            F.Sp, F.Rightarrow, F.RowBreak, F.Grp(),
            F.OpenBracket,
            F.Open, Defect(w), F.Sp, F.Eq, F.Sp, F.D(0), F.Sp, F.Leftrightarrow,
            F.Sp, F.Forall, F.Sp, y, F.Comma, F.Sp, wpAtY, F.Sp, F.Eq, F.Sp,
            F.D(0), F.Sp, F.Lor, F.Sp, Posterior(p, y), F.Sp, F.Eq, F.Sp,
            Posterior(q, y), F.Close, F.Sp, F.Land, F.RowBreak,
            F.Open, Defect(w), F.Sp, F.Eq, F.Sp, F.D(0), F.Sp, F.Leftrightarrow,
            F.Sp, F.Exists, F.Sp, r, F.Colon, F.Sp, F.Id("Y"), F.To, F.Sp,
            F.Id("X"), F.To, F.Sp, F.Mathbb, F.Grp(F.Id("R")), F.Comma, F.RowBreak,
            F.Open, F.Forall, F.Sp, y, F.Comma, F.Sp, x, F.Comma, F.Sp,
            r, F.Open, y, F.Comma, F.Sp, x, F.Close, F.Sp, F.Eq, F.Sp,
            F.Begin, F.Grp(F.Id("cases")), q, F.Open, x, F.Close, F.Comma,
            F.Sp, F.Amp, wqAtY, F.Sp, F.Eq, F.Sp, F.D(0), F.RowBreak,
            Posterior(q, y), F.Open, x, F.Close, F.Comma, F.Sp, F.Amp,
            F.Text, F.Grp(F.Id("otherwise")), F.End, F.Grp(F.Id("cases")), F.Close,
            F.Sp, F.Land, F.RowBreak,
            F.Open, F.Forall, F.Sp, y, F.Comma, F.Sp, x, F.Comma, F.Sp,
            F.D(0), F.Le, F.Sp, r, F.Open, y, F.Comma, F.Sp, x, F.Close, F.Close,
            F.Sp, F.Land, F.Sp,
            F.Open, F.Forall, F.Sp, y, F.Comma, F.Sp, F.Sum, F.Underscore,
            F.Grp(x), r, F.Open, y, F.Comma, F.Sp, x, F.Close,
            F.Sp, F.Eq, F.Sp, F.D(1), F.Close, F.Sp, F.Land, F.RowBreak,
            Output(r, Output(w, p)), F.Sp, F.Eq, F.Sp, p,
            F.Sp, F.Land, F.Sp, Output(r, Output(w, q)), F.Sp,
            F.Eq, F.Sp, q, F.Close, F.Sp, F.Land, F.RowBreak,
            F.Forall, F.Sp, e, F.Colon, F.Sp, F.Id("X"), F.Sp, F.Equiv, F.Sp,
            F.Id("Y"), F.Comma, F.Sp, Defect(pe), F.Sp, F.Eq, F.Sp, F.D(0),
            F.CloseBracket, F.Dot, F.End, F.Grp(F.Id("gathered"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero data-processing defect is characterized by posterior agreement and Bayesian "
            + "recovery, and it vanishes for permutation channels.",
        H("Posterior Equality, Recovery, and Permutation Channels"),
        Blocks(
            Paragraph(Text(
                "The three clauses are stated together: posterior equality on every positive "
                    + "output, exact recovery by the Bayesian reverse channel, and zero defect "
                    + "for every finite permutation channel.")),
            Describe.Lean(
                DescribeId.Create(
                    "zero-defect-equivalences-and-permutation-channel-equality"),
                DeclarationHandle.Create(LeanDeclaration),
                H("Zero defect, recovery, and permutation equality"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The posterior and recovery equivalences are imported exact results. "
                            + "For a permutation channel, the output law is the input law "
                            + "reindexed by the inverse equivalence. Mathlib's finite-sum "
                            + "reindexing theorem then makes the two divergences equal."))),
                DescribeRole.Theorem)
        )));
}
