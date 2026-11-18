using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class KingTwoColumnOneDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoColumnOne.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229755");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical four-colour paths with exactly two equal adjacent pairs.", H("Two-defect paths"),
        Blocks(Paragraph(Text("The prefix and adjacent-edge reconstructions, finite state transition counts and count-to-matrix induction establish the domain counting correspondence. The recurrence consumes this content together with the arithmetic matrix certificate.")),
            Node("result", "The width-one six-term recurrence", Formula0(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "A one-column king array is a path. Its canonical word starts with colour zero. After this first cell, a state records the number m of introduced colours and the remaining defect budget d, where 1 <= m <= 4 and 0 <= d <= 2. There are m-1 existing colours different from the preceding colour, one equal colour if a defect remains, and one new colour when m < 4. These transitions count two-colour words as well as words using three or four colours."),
            Paragraph(Text("The integer transfer has twelve states indexed by 3(m-1)+d. Its terminal vector is the indicator of d=0. A table of type Fin 10 -> Fin 12 -> Int records ten backward iterates. The certificate pins its initial vector, each successive multiplication by the transposed transfer, and the order-six relation from iterates 3 through 9. DefectTransfer.forward_shift propagates that relation to every later height. The row-major canonical-word equivalence identifies these counts with the literal grid count.")))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229755"), ResolutionKind.Proved));

    private static Formula Formula0()
    {
        Formula Term(int c, int j) => Mul(Num(c.ToString(System.Globalization.CultureInfo.InvariantCulture)), CastInt(Call("KingTwoGrid.T",
            Call("Nat.sub", V("n"), Num(j.ToString(System.Globalization.CultureInfo.InvariantCulture))), Num("1"))));
        var rhs = Sub(Add(Sub(Add(Sub(Term(12, 1), Term(57, 2)), Term(136, 3)),
            Term(171, 4)), Term(108, 5)), Term(27, 6));
        return All("n", Q("Nat"), Imp(Leq(Num("10"), V("n")),
            Eq(CastInt(Call("KingTwoGrid.T", V("n"), Num("1"))), rhs)));
    }

    private static Formula V(string s) => F.Id(s);
    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string s)
    {
        var parts = s.Split('_');
        Formula Word(string p) => Seq(p.Select(ch => ch >= '0' && ch <= '9'
            ? Num(new string(new[] { ch })) : V(new string(new[] { ch }))).ToArray());
        Formula result = Word(parts[^1]);
        for (var i = parts.Length - 2; i >= 0; --i)
            result = Seq(Word(parts[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Typed(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula CastInt(Formula a) => Call("Int.ofNat", a);
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

}
