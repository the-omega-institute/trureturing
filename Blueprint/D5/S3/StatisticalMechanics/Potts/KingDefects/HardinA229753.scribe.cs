using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class HardinA229753Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/HardinA229753.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229753");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four-colour width-six king arrays with exactly two monochromatic bonds.", H("Two-defect width-six king arrays"),
        Blocks(Paragraph(Text("The successor multiplicities and initial row counts define a 96-class transfer for labelled width-six arrays with exactly two monochromatic bonds. Its forward vectors satisfy an order-six relation, and colour normalization gives the recurrence for the literal grid count.")),
            Node("result", "The width-six six-term recurrence", Formula0(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The literal count T(n,6) includes exactly two monochromatic horizontal, vertical, diagonal or antidiagonal bonds and uses row-major colour introduction. The 96-class exact-budget transfer counts labelled colourings. For n >= 2, KingTwoGrid.labelled_eq_twentyFour divides by 24; three occurring colours suffice for the free permutation action. The recurrence holds for every n >= 12, including the threshold."),
            Paragraph(Text("A transfer state consists of a boundary row and the remaining defect budget. Each transition subtracts the horizontal monochromatic bonds of the new row and the monochromatic bonds between the two rows. The terminal indicator accepts precisely zero remaining budget, so the transfer counts exactly two monochromatic bonds.")),
            Paragraph(Text("The twelve-row forward table satisfies W(11)=-8W(5)+36W(6)-66W(7)+63W(8)-33W(9)+9W(10). DefectTransfer.forward_shift propagates this integer relation to every later height. The GridBridge identifies the row-list cost with the literal grid edge count. These are finite combinatorial states of the four-state Potts antiferromagnet at exactly two unsatisfied bonds; no empirical physical claim is asserted.")))));


    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin229753"), ResolutionKind.Proved));

    private static Formula Formula0()
    {
        Formula Term(int c, int j) => Mul(Num(c.ToString(System.Globalization.CultureInfo.InvariantCulture)), CastInt(Call("KingTwoGrid.T",
            Call("Nat.sub", V("n"), Num(j.ToString(System.Globalization.CultureInfo.InvariantCulture))), Num("6"))));
        var rhs = Sub(Add(Sub(Add(Sub(Term(9, 1), Term(33, 2)), Term(63, 3)),
            Term(66, 4)), Term(36, 5)), Term(8, 6));
        return All("n", Q("Nat"), Imp(Leq(Num("12"), V("n")),
            Eq(CastInt(Call("KingTwoGrid.T", V("n"), Num("6"))), rhs)));
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
