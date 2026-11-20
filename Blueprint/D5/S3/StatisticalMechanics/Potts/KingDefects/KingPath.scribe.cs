using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class KingPathDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/KingPath.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229578");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite colourings with exactly one monochromatic king bond.", H("One-defect king colourings: KingPath"),
        Blocks(
            Node("errors", "Recursive adjacent-equality cost", PathFormula("errors"),
                DescribeRole.Definition, AssessedProvenance.FromRepo(),
                "Starting from the preceding colour p, the recursion adds one exactly when the next colour equals p."),
            Node("bad", "The adjacent-equality sum", PathFormula("bad"),
                DescribeRole.Definition, AssessedProvenance.FromRepo(),
                "Each consecutive pair contributes its equality indicator; the sum is zero for words of length at most one."),
            Node("errors_eq", "The sum equals the recursive cost", PathFormula("errors_eq"),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "For an arbitrary colour type with decidable equality, the adjacent-equality sum equals the recursion started at the first letter. The two-defect path bridge reuses this original correspondence."),
            Node("normal_path", "Canonical words and canonical one-column grids", NormalFormula(),
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                "The row-major order on a one-column grid agrees with the order of its word positions, so the two restricted-growth conditions are equivalent."),
            Node("width_one_large", "The width-one count for at least three cells", Formula0(),
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "A one-column array is a word with exactly one equal adjacent pair. Burnside counting for permutations of four colours gives the formula for every word of length at least three."))));

    private static DocumentBlock Node(string name, string title, Formula formula, DescribeRole role,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula PathFormula(string name)
    {
        var c=V("C"); var n=V("n"); var p=V("p"); var f=V("f");
        Formula Word(Formula length) => new Formula.TypeArrow(Call("Fin",length),c);
        Formula Generic(Formula body) => All("C",Call("Type"),
            Seq(OpenBracket,Call("DecidableEq",c),CloseBracket,Comma,Sp,body));
        var eqCost=Conditional(Eq(p,V("c")),Num("1"),Num("0"));
        var zero=All("p",c,All("f",Word(Num("0")),Eq(Call("errors",p,f),Num("0"))));
        var step=All("n",Call("Nat"),All("p",c,All("c",c,All("f",Word(n),
            Eq(Call("errors",p,Call("Fin.cons",V("c"),f)),Add(eqCost,Call("errors",V("c"),f)))))));
        var sum=Seq(Sum,Underscore,Grp(Typed(V("i"),Call("Fin",Sub(n,Num("1"))))),Sp,
            Conditional(Eq(App(f,Call("KingGrid.lo",V("i"))),App(f,Call("KingGrid.hi",V("i")))),Num("1"),Num("0")));
        var body=name switch
        {
            "errors" => new Formula.Logic(Parenthesized(zero),FormulaLogicOperator.And,Parenthesized(step)),
            "bad" => All("n",Call("Nat"),All("f",Word(n),Eq(Call("bad",f),sum))),
            "errors_eq" => All("n",Call("Nat"),All("f",Word(Add(n,Num("1"))),
                Eq(Call("bad",f),Call("errors",App(f,Num("0")),Call("Fin.tail",f))))),
            _ => throw new System.ArgumentOutOfRangeException(nameof(name))
        };
        return Generic(body);
    }
    private static Formula Conditional(Formula p,Formula y,Formula n) =>
        Parenthesized(Seq(Q("if"),Sp,Parenthesized(p),Sp,Q("then"),Sp,y,Sp,Q("else"),Sp,n));

    private static Formula NormalFormula() => All("n", Q("Nat"),
        All("f", new Formula.TypeArrow(Call("Fin", V("n")), Call("Fin", Num("4"))),
            new Formula.Logic(Call("KingGrid.normal", Parenthesized(Seq(LambdaLower, Sp,
                Typed(V("p"), Call("KingGrid.Cell", V("n"), Num("1"))), Sp, Mapsto, Sp,
                Call("f", Call("Prod.fst", V("p")))))), FormulaLogicOperator.Iff,
                Call("HardinA233177Canonical.Canonical", V("f")))));

    private static Formula Formula0() =>
        All("n", Q("Nat"), Imp(Leq(Num("3"), V("n")),
            Eq(Mul(Num("54"), CastInt(Call("KingGrid.T", V("n"), Num("1")))),
                Add(Mul(Sub(CastInt(V("n")), Num("1")),
                        Power(Typed(Num("3"), Q("Int")), V("n"))),
                    Mul(Num("27"), Sub(CastInt(V("n")), Num("1")))))));

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
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

}
