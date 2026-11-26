using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.KingDefects;

internal sealed class KingTwoGridDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/KingDefects/KingTwoGrid.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/SpinModels/hardin2013a229755");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal two-defect king colourings and colour-orbit normalization.", H("Two-defect colour normalization"),
        Blocks(
            Node("TwoDefect","Exactly two equal-colour bonds",DefectFormula(),DescribeRole.Definition,AssessedProvenance.FromLiterature(Source),
                "The filter counts the four disjoint king-edge constructors, with no orientation duplication."),
            Node("L","Labelled two-defect count",CountFormula(false),DescribeRole.Definition,AssessedProvenance.FromRepo(Source),
                "All four colour names remain distinguished."),
            Node("T","Canonical two-defect count",CountFormula(true),DescribeRole.Definition,AssessedProvenance.FromLiterature(Source),
                "Row-major restricted growth selects one representative of every colour orbit."),
            Node("labelled_eq_twentyFour","Twenty-four labelled maps per canonical map",NormalizationFormula(),DescribeRole.Theorem,AssessedProvenance.FromRepo(Source),
                "Both dimensions are at least two and the single 2 by 2 block is excluded. Every two-colour 2 by 3 colouring has at least three monochromatic king edges. An injective edge embedding, with transposition for a narrow rectangle, forces three occurring colours. The original KingGrid.canonical_count_three then gives the factor twenty-four. The exceptional 2 by 2 normalization and the global two-defect slot count remain separate obligations."))));
    private static DocumentBlock Node(string name,string title,Formula formula,DescribeRole role,AssessedProvenance provenance,string prose) =>
        Describe.Lean(DescribeId.Create(name.Replace("_","-").ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),
            H(title),StatementSource.FromAuthor(Disp(formula)),provenance,Blocks(Paragraph(Text(prose))),role);
    private static Formula Maps() => Arrow(Call("KingGrid.Cell",V("n"),V("k")),Call("Fin",Num("4")));
    private static Formula Dims(Formula body) => All("n",Q("Nat"),All("k",Q("Nat"),body));
    private static Formula DefectFormula() => Dims(All("f",Maps(),Iff(Call("KingTwoGrid.TwoDefect",V("f")),
        Eq(Call("Finset.card",Call("Finset.filter",Fn("e",Call("KingGrid.Edge",V("n"),V("k")),
            Call("KingGrid.mono",V("f"),V("e"))),Call("Finset.univ",Call("KingGrid.Edge",V("n"),V("k"))))),Num("2")))));
    private static Formula CountFormula(bool canonical)
    {
        var pred = Call("KingTwoGrid.TwoDefect",V("f"));
        if(canonical) pred=And(pred,Call("KingGrid.normal",V("f")));
        return Dims(Eq(Call(canonical?"KingTwoGrid.T":"KingTwoGrid.L",V("n"),V("k")),
            Call("Nat.card",Subtype("f",Maps(),pred))));
    }
    private static Formula NormalizationFormula()
    {
        var distinct = new Formula.Logic(Ne(V("n"),Num("2")),FormulaLogicOperator.Or,Ne(V("k"),Num("2")));
        var result = Eq(Call("KingTwoGrid.L",V("n"),V("k")),
            Mul(Num("24"),Call("KingTwoGrid.T",V("n"),V("k"))));
        return Dims(Imp(Leq(Num("2"),V("n")),Imp(Leq(Num("2"),V("k")),Imp(distinct,result))));
    }
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
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
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(Parenthesized(a), Parenthesized(b));
    private static Formula Subtype(string x, Formula t, Formula b) =>
        Seq(OpenBrace, V(x), Colon, Sp, t, Sp, Slash, Slash, Sp, Parenthesized(b), CloseBrace);
    private static Formula Fn(string x, Formula t, Formula b) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(x),t), Sp, Mapsto, Sp, b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula All(string x, Formula t, Formula b) =>
        Seq(Forall, Sp, Typed(V(x), t), Comma, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));

}
