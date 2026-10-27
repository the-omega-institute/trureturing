using F = StrataLint.Scribe.FormulaDsl;
using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases.MazorchukXuFamiliesNotation;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.BinomialBases;

internal static class MazorchukXuFamiliesNotation
{
    internal static Formula N => Fn("Nat");
    internal static Formula Q => Fn("Rat");
    internal static Formula Prop => Fn("Prop");
    internal static Formula Ty => Fn("Type");
    internal static Formula Pairs => Fn("Prod", N, N);
    internal static Formula Points => Fn("Finset", Pairs);
    internal static Formula V(string name) => F.Id(name);
    internal static Formula Fn(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    internal static Formula Apply(Formula fn, params Formula[] args) =>
        Seq(fn, Open, new Formula.LatexSequence([.. args.SelectMany((a, i) =>
            i == 0 ? new[] { a } : new[] { Comma, Sp, a })]), Close);
    internal static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    internal static Formula Many(string names, Formula domain, Formula body)
    {
        foreach (var name in names.Split(' ').Reverse()) body = All(name, domain, body);
        return body;
    }
    internal static Formula Par(Formula a) => Seq(Open, a, Close);
    internal static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) =>
        new Formula.Logic(Par(a), op, Par(b));
    internal static Formula And(params Formula[] xs) =>
        xs.Aggregate((a, b) => Logic(a, FormulaLogicOperator.And, b));
    internal static Formula Or(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Or, b);
    internal static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    internal static Formula Iff(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    internal static Formula Not(Formula a) => Seq(Neg, Sp, Par(a));
    internal static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    internal static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    internal static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    internal static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    internal static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
    internal static Formula Plus(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    internal static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    internal static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    internal static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    internal static Formula Set(string name, Formula domain, Formula predicate) =>
        Seq(OpenBrace, V(name), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace);
    internal static Formula Rel(Formula a) => new Formula.TypeArrow(a, new Formula.TypeArrow(a, Prop));
    internal static Formula Map(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    internal static Formula Ordered(string name, Formula body) =>
        All(name, Ty, Seq(OpenBracket, Fn("LinearOrder", V(name)), CloseBracket, Sp, body));
    internal static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/mazorchukxu2026cokernel");
    internal static DocumentBlock Node(string module, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature = false) =>
        Describe.Lean(DescribeId.Create("mazorchuk-xu-" + module.ToLowerInvariant() + "-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Combinatorics/BinomialBases/MazorchukXu" + module + "." + name),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}

internal sealed class MazorchukXuFamiliesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shifting every upper coordinate by one gives an exact counted equivalence between the literal triangular family and bounded ordered-edge closure.",
        H("The counted point-to-edge bridge"),
        Blocks(
            Node("Families", "edgeTriangle", "The strict edge triangle", EdgeTriangle(),
                "The vertex set is zero through n+1, and every selected edge has strictly increasing endpoints.", DescribeRole.Definition),
            Node("Families", "edgeSet", "Points become edges", Shift(true),
                "Shift the second coordinate up by one. This map is injective on all natural pairs and preserves the zero first coordinate.", DescribeRole.Definition),
            Node("Families", "pointSet", "Edges become points", Shift(false),
                "Shift the second coordinate down by one. On strict natural edges this is inverse to edgeSet.", DescribeRole.Definition),
            Node("Families", "edgeFamily", "The bounded ordered-edge family", EdgeFamily(),
                "The notation pairMembership(A)(a,b) means (a,b) belongs to A. Every subset of the strict edge triangle is tested against both rules and the exact first-column statistic.", DescribeRole.Definition),
            Node("Families", "count_eq_edgeFamily_card", "Equality of the finite counts", Many("n k", N,
                Eq(Fn("count",V("n"),V("k")),Fn("card",Fn("edgeFamily",V("n"),V("k"))))),
                "The two coordinate shifts are inverse on their bounded domains, preserve closure in both directions and preserve the first-column count. A finite-set bijection therefore gives the equality for all natural n and k. This includes empty subsets, zero first-column counts, n=0 and every valid deficit. It introduces no representation-theoretic assumption.", DescribeRole.Theorem)), []));

    private static Formula EdgeTriangle() => All("n",N,Eq(Fn("edgeTriangle",V("n")),
        Set("p",Pairs,And(Lt(Fn("fst",V("p")),Fn("snd",V("p"))),Le(Fn("snd",V("p")),Plus(V("n"),D(1)))))));
    private static Formula Shift(bool up)
    {
        var p=V("p");var q=V("q");
        return All(up?"Y":"A",Points,Eq(Fn(up?"edgeSet":"pointSet",V(up?"Y":"A")),
            Set("q",Pairs,Ex("p",V(up?"Y":"A"),Eq(q,Pair(Fn("fst",p),
                up?Plus(Fn("snd",p),D(1)):Sub(Fn("snd",p),D(1))))))));
    }
    private static Formula EdgeFamily() => Many("n k",N,Eq(Fn("edgeFamily",V("n"),V("k")),
        Set("A",Points,And(Subset(V("A"),Fn("edgeTriangle",V("n"))),
            Fn("Rules",Fn("pairMembership",V("A"))),Eq(Fn("firstColumnCard",V("A")),V("k"))))));
}
