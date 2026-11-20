using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class HardinA229750Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229750.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229750");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-colour width-3 king arrays with exactly two monochromatic bonds.", H("Two-defect width-3 king arrays"),
        Blocks(Paragraph(Text("The exact-budget transfer records successor multiplicities and first-row weights. The list-to-grid identity and colour normalization express its labelled count as 24 times the canonical count. A linear relation among the forward vectors then gives the recurrence.")),
            Node("result", "The width-3 six-term recurrence", Formula0(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The literal count T(n,3) includes exactly two monochromatic horizontal, vertical, diagonal or antidiagonal bonds and uses row-major colour introduction. The 9-class exact-budget transfer counts labelled colourings. For n >= 2, KingTwoGrid.labelled_eq_twentyFour divides by 24; three occurring colours suffice for the free permutation action. The recurrence holds for every n >= 9, including the threshold."),
            Node("closed_form", "The width-3 closed form", Formula1(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "For every n >= 3, eight times the literal orbit count equals the displayed polynomial-exponential expression. The recurrence and the six values T(3,3)=598, T(4,3)=2347, T(5,3)=6809, T(6,3)=17404, T(7,3)=41872 and T(8,3)=97565 determine the solution by Mathlib LinearRecurrence.eq_iff_eqOn_range_order."),
            Paragraph(Text("The nine-row forward table satisfies W(8)=-8W(2)+36W(3)-66W(4)+63W(5)-33W(6)+9W(7). DefectTransfer.forward_shift propagates this integer relation to every later height. The GridBridge identifies the row-list cost with the literal grid edge count. These are finite combinatorial states of the four-state Potts antiferromagnet at exactly two unsatisfied bonds; no empirical physical claim is asserted.")))));


    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Formula0()
    {
        Formula Term(int c, int j) => Mul(Num(c.ToString(System.Globalization.CultureInfo.InvariantCulture)), CastInt(Call("KingTwoGrid.T",
            Call("Nat.sub", V("n"), Num(j.ToString(System.Globalization.CultureInfo.InvariantCulture))), Num("3"))));
        var rhs = Sub(Add(Sub(Add(Sub(Term(9, 1), Term(33, 2)), Term(63, 3)),
            Term(66, 4)), Term(36, 5)), Term(8, 6));
        return All("n", Q("Nat"), Imp(Leq(Num("9"), V("n")),
            Eq(CastInt(Call("KingTwoGrid.T", V("n"), Num("3"))), rhs)));
    }

    private static Formula Formula1()
    {
        var power = Call("HPow.hPow", Num("2"), V("n"));
        var n = CastInt(V("n"));
        var rhs = Add(Add(Mul(Num("2"), Add(Num("1732"), Mul(Num("117"), power))),
            Mul(Sub(Mul(Num("279"), power), Num("4084")), n)),
            Mul(Add(Mul(Num("9"), power), Num("484")), Call("HPow.hPow", n, Num("2"))));
        return All("n", Q("Nat"), Imp(Leq(Num("3"), V("n")),
            Eq(Mul(Num("8"), CastInt(Call("KingTwoGrid.T", V("n"), Num("3")))), rhs)));
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
