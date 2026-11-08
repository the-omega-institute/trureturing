using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Periodic;

internal sealed class BalaA281184TotientSquarePeriodDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Periodic/BalaA281184TotientSquarePeriod.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/bala2026totientsquareperiod");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Totient-square periods of integral derivation coefficients.",
        H("Bala A281184 Totient-Square Period"),
        Blocks(
            Node("claim", "claim", Formula0(),
                "E.g.f. C(x)^3 = d/dx log(C(x) + S(x)), where C(x) and S(x) are described by A281181 and A281180, respectively. Conjecture: the sequence {a(n)} taken modulo a positive integer k is eventually periodic with the period dividing phi(k)^2, where phi(n) = A000010(n). An example is given below. - _Peter Bala_, Feb 16 2026 The source is unpaginated. The primitive has constant coefficient zero, eCoeff is factorial times the ordinary coefficient, and all sequences take integer values. Natural subtraction is truncated subtraction.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "result", Formula1(),
                "The integral derivation flow supplies the series and its integer exponential coefficients. Prime-power operator annihilators give the prescribed shift, and divisibility assembles all positive moduli.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("balaa281184totientsquareperiod-" + name.Replace("C", "uppercase-c").Replace("S", "uppercase-s").Replace('.', '-').Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name[(name.LastIndexOf('.') + 1)..]), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role,
        null);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count != 0) items.Add(Dot);
            items.Add(Operatorname);
            items.Add(Grp(F.Id(part)));
        }
        return Seq(items.ToArray());
    }
    private static Formula Formula0() => Disp(Seq(F.Id("claim"), Sp, Eq, Sp, Parenthesized(Seq(Exists, Sp, Parenthesized(Seq(F.Id("H"), Sp, F.Id("C"), Sp, F.Id("S"), Sp, Colon, Sp, F.Id("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, Qualified("PowerSeries","constantCoeff"), Sp, F.Id("H"), Sp, Eq, Sp, D(0), Sp, Land, Sp, Qualified("PowerSeries","derivative"), Sp, F.Id("H"), Sp, Eq, Sp, new Formula.Power(F.Id("C"),D(3)), Sp, Land, Sp, F.Id("C"), Sp, Eq, Sp, Qualified("PowerSeries","C"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Cdot, Sp, Parenthesized(Seq(Qualified("PowerSeries","subst"), Sp, F.Id("H"), Sp, Parenthesized(Seq(Qualified("PowerSeries","exp"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Plus, Sp, Qualified("PowerSeries","subst"), Sp, Parenthesized(Seq(Minus, Sp, F.Id("H"))), Sp, Parenthesized(Seq(Qualified("PowerSeries","exp"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Land, Sp, Qualified("PowerSeries","constantCoeff"), Sp, F.Id("S"), Sp, Eq, Sp, D(0), Sp, Land, Sp, Qualified("PowerSeries","derivative"), Sp, F.Id("S"), Sp, Eq, Sp, new Formula.Power(Parenthesized(Seq(D(1), Sp, Plus, Sp, new Formula.Power(F.Id("S"),D(2)))),D(2)), Sp, Land, Sp, Qualified("PowerSeries","derivative"), Sp, Parenthesized(Seq(Qualified("PowerSeries","logOf"), Sp, Parenthesized(Seq(F.Id("C"), Sp, Plus, Sp, F.Id("S"))))), Sp, Eq, Sp, new Formula.Power(F.Id("C"),D(3)), Sp, Land, Sp, Parenthesized(Seq(Exists, Sp, F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Eq, Sp, F.Id("eCoeff"), Sp, Parenthesized(Seq(new Formula.Power(F.Id("C"),D(3)))), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(1), Sp, Le, Sp, F.Id("k"), Sp, Implies, Sp, Exists, Sp, F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, F.Id("N"), Sp, Le, Sp, F.Id("n"), Sp, Implies, Sp, Qualified("Int","ModEq"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Parenthesized(Seq(F.Id("a"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Nat","totient"), Sp, F.Id("k"))),D(2)))))), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("n")))))))))));

    private static Formula Formula1() => Disp(Seq(Exists, Sp, Parenthesized(Seq(F.Id("H"), Sp, F.Id("C"), Sp, F.Id("S"), Sp, Colon, Sp, F.Id("PowerSeries"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp, Qualified("PowerSeries","constantCoeff"), Sp, F.Id("H"), Sp, Eq, Sp, D(0), Sp, Land, Sp, Qualified("PowerSeries","derivative"), Sp, F.Id("H"), Sp, Eq, Sp, new Formula.Power(F.Id("C"),D(3)), Sp, Land, Sp, F.Id("C"), Sp, Eq, Sp, Qualified("PowerSeries","C"), Sp, Parenthesized(Seq(D(1), Sp, Slash, Sp, D(2), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Cdot, Sp, Parenthesized(Seq(Qualified("PowerSeries","subst"), Sp, F.Id("H"), Sp, Parenthesized(Seq(Qualified("PowerSeries","exp"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Plus, Sp, Qualified("PowerSeries","subst"), Sp, Parenthesized(Seq(Minus, Sp, F.Id("H"))), Sp, Parenthesized(Seq(Qualified("PowerSeries","exp"), Sp, Seq(Mathbb, Grp(F.Id("Q"))))))), Sp, Land, Sp, Qualified("PowerSeries","constantCoeff"), Sp, F.Id("S"), Sp, Eq, Sp, D(0), Sp, Land, Sp, Qualified("PowerSeries","derivative"), Sp, F.Id("S"), Sp, Eq, Sp, new Formula.Power(Parenthesized(Seq(D(1), Sp, Plus, Sp, new Formula.Power(F.Id("S"),D(2)))),D(2)), Sp, Land, Sp, Qualified("PowerSeries","derivative"), Sp, Parenthesized(Seq(Qualified("PowerSeries","logOf"), Sp, Parenthesized(Seq(F.Id("C"), Sp, Plus, Sp, F.Id("S"))))), Sp, Eq, Sp, new Formula.Power(F.Id("C"),D(3)), Sp, Land, Sp, Parenthesized(Seq(Exists, Sp, F.Id("a"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Eq, Sp, F.Id("eCoeff"), Sp, Parenthesized(Seq(new Formula.Power(F.Id("C"),D(3)))), Sp, Parenthesized(Seq(D(2), Sp, Cdot, Sp, F.Id("n"))))), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, D(1), Sp, Le, Sp, F.Id("k"), Sp, Implies, Sp, Exists, Sp, F.Id("N"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, Forall, Sp, F.Id("n"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, F.Id("N"), Sp, Le, Sp, F.Id("n"), Sp, Implies, Sp, Qualified("Int","ModEq"), Sp, Parenthesized(Seq(F.Id("k"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Parenthesized(Seq(F.Id("a"), Sp, Parenthesized(Seq(F.Id("n"), Sp, Plus, Sp, new Formula.Power(Parenthesized(Seq(Qualified("Nat","totient"), Sp, F.Id("k"))),D(2)))))), Sp, Parenthesized(Seq(F.Id("a"), Sp, F.Id("n")))))))));
}
