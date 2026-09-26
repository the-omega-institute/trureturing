using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeFiniteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFinite.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var type = V("V"); var g = V("G"); var v = V("v"); var w = V("w");
        var f = V("F"); var s = V("S"); var m = V("m"); var r = V("r");
        var u = V("u"); var a = V("a"); var rows = V("rows"); var row = V("row");
        var rowType = Seq(Nat(), Times, Sp, Nat());
        var finite = Call("Finite", type);
        var vertex = Name("V13");
        return DocumentDefinition.Create(ScribeNode.Create(
            "The numeric predicates agree with graph neighborhoods, vertex sets, and complete initial-force families.",
            H("Forts and Mask Completeness"),
            Blocks(
            Node("finite-neighbors", "Finite graph neighborhood", "finiteNeighbors",
                Disp(Q(Imp(finite, Eq(Call("finiteNeighbors", g, v), SetOf("w", type, Adj(g, v, w)))), ("V", Name("Type")), ("G", Call("SimpleGraph", type)), ("v", type))),
                "For a finite simple graph, the neighborhood consists of exactly the adjacent vertices.",
                DescribeRole.Definition),
            Node("fort", "A set that resists forcing", "IsFort",
                Disp(Q(Imp(finite, Iff(Call("IsFort", g, f), And(Call("Nonempty", f), Q(Imp(Not(Mem(v, f)), Ne(Card(Inter(Call("finiteNeighbors", g, v), f)), Num(1))), ("v", type))))), ("V", Name("Type")), ("G", Call("SimpleGraph", type)), ("F", Fs(type)))),
                "A fort is nonempty, and no vertex outside it has exactly one neighbor in it.",
                DescribeRole.Definition),
            Node("neighbors-spec", "Agreement of the neighbor table", "neighbors13_spec",
                Disp(Q(Iff(Mem(w, Call("neighbors13", v)), Adj(Call("gp", Num(13), Num(3)), v, w)), ("v", vertex), ("w", vertex))),
                "The three listed neighbors are exactly the graph neighbors in P(13,3).",
                DescribeRole.Theorem),
            Node("bit-count-card", "Bits count decoded vertices", "bitCount26_eq_card_maskSet13",
                Disp(Q(Eq(Call("bitCount26", m), Card(Call("maskSet13", m))), ("m", Nat()))),
                "The number of low set bits equals the cardinality of the decoded vertex set.",
                DescribeRole.Theorem),
            Node("fort-sound", "A valid mask is a fort", "fortOK_sound",
                Disp(Q(Imp(Eq(Call("fortOK", m), True()), Call("IsFort", Call("gp", Num(13), Num(3)), Call("maskSet13", m))), ("m", Nat()))),
                "The fort predicate guarantees a nonempty decoded set with no unique outside neighbor.",
                DescribeRole.Theorem),
            Node("set-mask", "Encode a finite vertex set", "setMask13",
                Disp(Q(Eq(Call("setMask13", s), SumOver("v", s, Pow(Num(2), Call("code13", v)))), ("S", Fs(vertex)))),
                "The mask of a set is the sum of the powers of two at its vertex positions.",
                DescribeRole.Definition),
            Node("set-mask-bit", "Membership is recovered bit by bit", "testBit_setMask13",
                Disp(Q(Iff(Eq(Call("testBit", Call("setMask13", s), Call("code13", v)), True()), Mem(v, s)), ("S", Fs(vertex)), ("v", vertex))),
                "Encoding a finite set recovers exactly its membership bits.",
                DescribeRole.Theorem),
            Node("set-mask-bound", "Every set mask fits in twenty-six bits", "setMask13_lt_two_pow",
                Disp(Q(Lt(Call("setMask13", s), Pow(Num(2), Num(26))), ("S", Fs(vertex)))),
                "No vertex position reaches twenty-six, so the encoded mask is below two to the twenty-sixth power.",
                DescribeRole.Theorem),
            Node("rotate-set", "Rotate all selected vertices", "rotateFinset13",
                Disp(Q(Eq(Call("rotateFinset13", r, s), Image(s, "v", Call("rotate13", r, v))), ("r", Fin(Num(13))), ("S", Fs(vertex)))),
                "Apply the same column rotation to every vertex of the finite set.",
                DescribeRole.Definition),
            Node("first-force-anchor", "Every oriented edge has an anchor", "initialForce_anchor13",
                Disp(Q(Imp(Adj(Call("gp", Num(13), Num(3)), u, w), Ex("a", Name("Anchor13"), And(Eq(Call("anchorTarget", a), Call("rotate13", Second(u), w)), Eq(Call("anchorRequired", a), Call("insert", Call("rotate13", Second(u), u), Image(Call("erase", Call("neighbors13", u), w), "v", Call("rotate13", Second(u), v))))))), ("u", vertex), ("w", vertex))),
                "Rotate the source of an oriented edge to column zero. One of the six anchors has the rotated target and the rotated source together with its other two neighbors.",
                DescribeRole.Theorem),
            Node("ordered-completeness", "An ordered family contains every candidate", "orderedRows_complete",
                Disp(Q(Imp(And(Eq(Call("familyOrderOK", rows), True()), Q(Imp(Mem(row, rows), Eq(Call("candidateShapeOK", a, First(row)), True())), ("row", rowType)), Eq(Call("candidateShapeOK", a, m), True())), Ex("f", Nat(), Mem(Pair(m, V("f")), rows))), ("a", Name("Anchor13")), ("rows", List(rowType)), ("m", Nat()))),
                "A family of 7315 strictly increasing keys, all of the chosen anchor shape, contains every mask with that shape.",
                DescribeRole.Theorem)),
            []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Name(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula V(string name) => F.Id(name);
    private static Formula Num(long value) => new Formula.Number(value);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Q(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Mem(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Not(Formula value) => new Formula.Not(value);
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(value, power);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Fs(Formula value) => Call("Finset", value);
    private static Formula List(Formula value) => Call("List", value);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula First(Formula value) => Call("fst", value);
    private static Formula Second(Formula value) => Call("snd", value);
    private static Formula SetOf(string variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, Sp, V(variable), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace, Sp);
    private static Formula Image(Formula set, string variable, Formula value) =>
        new Formula.SetBuilder(value, V(variable), set);
    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(V(variable), Sp, InMacro, Sp, domain), body);
    private static Formula Inter(Formula left, Formula right) => Call("inter", left, right);
    private static Formula True() => Name("true");
    private static Formula Adj(Formula graph, Formula left, Formula right) => Call("Adj", graph, left, right);
}
