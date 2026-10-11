using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Hamming;

internal sealed class InducedSubcubesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Hamming/InducedSubcubes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Induced Boolean cubes are exactly coordinate down-cubes, with unique top and direction set.",
        H("Induced subcubes of the Boolean hypercube"),
        Blocks(
            Node("erase", "Coordinate erasure", "erase", EraseFormula(),
                "erase v T changes v to false on the coordinates in T and leaves every other coordinate unchanged.", DescribeRole.Definition),
            Node("down-cube", "Coordinate down-cube", "downCube", DownCubeFormula(),
                "downCube v S is the set of words obtained by erasing an arbitrary subset T of S from v.", DescribeRole.Definition),
            Node("erase-empty", "Erasing no coordinates", "erase_empty", EraseEmptyFormula(),
                "Erasing the empty set leaves every Boolean word unchanged.", DescribeRole.Theorem),
            Node("top-member", "Top vertex of a down-cube", "top_mem_downCube", TopMemDownCubeFormula(),
                "The top vertex belongs to its coordinate down-cube.", DescribeRole.Theorem),
            Node("cube-map-image", "Image of a cube map", "cube_map_image", CubeMapImageFormula(),
                "An injective map from a Boolean k-cube to a Boolean n-cube that preserves Hamming-distance-one edges has an image cut out by k distinct coordinate directions; every other coordinate is fixed to its value at the all-false source vertex.", DescribeRole.Theorem),
            Node("down-cube-unique", "Uniqueness of the top and directions", "downCube_unique", DownCubeUniqueFormula(),
                "If two down-cubes have direction sets contained in the true coordinates of their respective top vertices and are equal as sets, then their top vertices and direction sets are equal.", DescribeRole.Theorem),
            Node("induced-cube-iff", "Classification of induced cubes", "induced_cube_iff", InducedCubeIffFormula(),
                "For every set U of Boolean words, the induced hypercube on U is isomorphic to hypercube k exactly when there is a unique pair (v,S) with S.card = k, S contained in the true coordinates of v, and U = downCube v S.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula? formula, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Id(string name) => F.Id(name);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Not(Formula a) => new Formula.Not(a);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Id("fun"), Sp, Parenthesized(Seq(Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula SetOf(string name, Formula type, Formula predicate) =>
        Seq(OpenBrace, Id(name), Colon, Sp, type, Sp, Bar, Sp, predicate, CloseBrace);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);

    private static Formula WordType(Formula n) => Arrow(Call("Fin", n), Id("Bool"));
    private static Formula FinsetType(Formula n) => Call("Finset", Call("Fin", n));

    private static Formula EraseFormula()
    {
        var n = Id("n"); var v = Id("v"); var t = Id("T");
        var q = Id("q");
        var body = Lambda("q", Call("Fin", n),
            Seq(Id("if"), Sp, Member(q, t), Sp, Id("then"), Sp, Id("false"), Sp,
                Id("else"), Sp, Call("v", q)));
        return Disp(All("n", Nat(), All("v", WordType(n), All("T", FinsetType(n),
            Eq(Call("erase", v, t), body)))));
    }

    private static Formula DownCubeFormula()
    {
        var n = Id("n"); var v = Id("v"); var s = Id("S");
        var t = Id("T");
        var w = Id("w");
        var witness = Exists("T", FinsetType(n),
            And(Call("Finset.Subset", t, s), Eq(w, Call("erase", v, t))));
        return Disp(All("n", Nat(), All("v", WordType(n), All("S", FinsetType(n),
            Eq(Call("downCube", v, s), SetOf("w", WordType(n), witness))))));
    }

    private static Formula TrueCoordinates(Formula v, Formula n)
    {
        return Call("Finset.filter", Lambda("q", Call("Fin", n), Eq(new Formula.Apply(v, [Id("q")]), Id("true"))),
            Call("Finset.univ"));
    }

    private static Formula EraseEmptyFormula()
    {
        var n = Id("n"); var v = Id("v");
        return Disp(All("n", Nat(), All("v", WordType(n),
            Eq(Call("erase", v, Emptyset), v))));
    }

    private static Formula TopMemDownCubeFormula()
    {
        var n = Id("n"); var v = Id("v"); var s = Id("S");
        return Disp(All("n", Nat(), All("v", WordType(n), All("S", FinsetType(n),
            Member(v, Call("downCube", v, s))))));
    }

    private static Formula CubeMapImageFormula()
    {
        var k = Id("k"); var n = Id("n");
        var f = Id("f"); var u = Id("u"); var v = Id("v"); var w = Id("w"); var q = Id("q");
        var wordK = WordType(k); var wordN = WordType(n);
        var edge = All("u", wordK, All("v", wordK,
            Implies(Eq(Call("hammingDist", u, v), D(1)),
                Eq(Call("hammingDist", Call("f", u), Call("f", v)), D(1)))));
        var allFalse = Call("Function.const", Call("Fin", k), Id("false"));
        var image = Iff(
            Member(w, Call("Set.range", f)),
            All("q", Call("Fin", n),
                Implies(
                    Not(Member(q, Call("Set.range", Id("d")))),
                    Eq(Call("w", q), Call("f", allFalse, q)))));
        var body = All("f", Arrow(wordK, wordN),
            Implies(Call("Function.Injective", f),
                Implies(edge,
                    Exists("d", Call("Function.Embedding", Call("Fin", k), Call("Fin", n)),
                        All("w", wordN, image)))));
        return Disp(All("k", Nat(), All("n", Nat(), body)));
    }

    private static Formula DownCubeUniqueFormula()
    {
        var n = Id("n"); var v = Id("v"); var v2 = Id("vPrime");
        var s = Id("S"); var s2 = Id("SPrime");
        var word = WordType(n); var finset = FinsetType(n);
        var supportV = Call("Finset.Subset", s, TrueCoordinates(v, n));
        var supportV2 = Call("Finset.Subset", s2, TrueCoordinates(v2, n));
        var antecedent = And(supportV, And(supportV2,
            Eq(Call("downCube", v, s), Call("downCube", v2, s2))));
        var consequent = And(Eq(v, v2), Eq(s, s2));
        return Disp(All("n", Nat(), All("v", word, All("vPrime", word,
            All("S", finset, All("SPrime", finset,
                Implies(antecedent, consequent)))))));
    }

    private static Formula InducedCubeIffFormula()
    {
        var k = Id("k"); var n = Id("n"); var u = Id("U");
        var word = WordType(n); var pair = Call("Prod", word, FinsetType(n));
        var p = Id("p");
        var iso = Call("Nonempty", Call("SimpleGraph.Iso",
            Call("SimpleGraph.induce", Call("hypercube", n), u), Call("hypercube", k)));
        var property = And(Eq(Call("Finset.card", Call("Prod.snd", p)), k),
            And(Call("Finset.Subset", Call("Prod.snd", p), TrueCoordinates(Call("Prod.fst", p), n)),
                Eq(u, Call("downCube", Call("Prod.fst", p), Call("Prod.snd", p)))));
        var unique = Seq(F.Exists, Bang, Sp, Parenthesized(Seq(p, Colon, Sp, pair)), Comma, Sp, property);
        return Disp(All("k", Nat(), All("n", Nat(), All("U", Call("Set", word),
            Iff(iso, unique)))));
    }
}
