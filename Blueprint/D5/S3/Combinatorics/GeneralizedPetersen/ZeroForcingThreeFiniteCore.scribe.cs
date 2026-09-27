using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeFiniteCoreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeFiniteCore.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var r = V("r"); var v = V("v"); var w = V("w"); var i = V("i");
        var m = V("m"); var s = V("s"); var f = V("f"); var row = V("row");
        var rows = V("rows"); var a = V("a"); var chunks = V("chunks");
        var start = V("start"); var len = V("len"); var j = V("j");
        var vertex = Name("V13");
        var rowType = Seq(Nat(), Times, Sp, Nat());
        var anchors = Set(Name("outerSpoke"), Name("outerNext"), Name("outerPrev"),
            Name("innerSpoke"), Name("innerNext"), Name("innerPrev"));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Twenty-six bit positions encode vertices, forts, and six oriented initial-force families.",
            H("Masks and Initial-Force Anchors at Thirteen Columns"),
            Blocks(
            Node("vertex-type", "The twenty-six vertices", "V13",
                Disp(Eq(Name("V13"), Vertices(Num(13)))),
                "The false layer is the outer cycle and the true layer is the inner layer, each indexed by Fin 13.",
                DescribeRole.Definition),
            Node("rotation", "Column rotation", "rotate13",
                Disp(Q(Eq(Call("rotate13", r, v), Pair(First(v), Sub(Second(v), r))), ("r", Fin(Num(13))), ("v", vertex))),
                "Rotation subtracts the chosen column from the index in each layer.",
                DescribeRole.Definition),
            Node("vertex-code", "Bit position of a vertex", "code13",
                Disp(Q(Eq(Call("code13", v), If(Eq(First(v), True()), Add(Num(13), Val(Second(v))), Val(Second(v)))), ("v", vertex))),
                "Outer vertices occupy bits zero through twelve; inner vertices occupy bits thirteen through twenty-five.",
                DescribeRole.Definition),
            Node("mask-set", "Decode a vertex mask", "maskSet13",
                Disp(Q(Eq(Call("maskSet13", m), SetOf("v", vertex, Eq(Call("testBit", m, Call("code13", v)), True()))), ("m", Nat()))),
                "A vertex belongs to the decoded set exactly when its corresponding bit is set.",
                DescribeRole.Definition),
            Node("neighbors", "The three neighbors", "neighbors13",
                Disp(Q(Eq(Call("neighbors13", v), If(Eq(First(v), True()), Set(Pair(False(), Second(v)), Pair(True(), Add(Second(v), Num(3))), Pair(True(), Sub(Second(v), Num(3)))), Set(Pair(True(), Second(v)), Pair(False(), Add(Second(v), Num(1))), Pair(False(), Sub(Second(v), Num(1)))))), ("v", vertex))),
                "Each vertex has its spoke mate and the two cyclic neighbors at step one in the outer layer or step three in the inner layer.",
                DescribeRole.Definition),
            Node("neighbor-codes", "Numeric neighbor positions", "neighborCodes13",
                Disp(Q(Eq(Call("neighborCodes13", i), If(Lt(i, Num(13)), ListOf(Mod(Add(i, Num(12)), Num(13)), Mod(Add(i, Num(1)), Num(13)), Add(Num(13), i)), ListOf(Sub(i, Num(13)), Add(Num(13), Mod(Add(Sub(i, Num(13)), Num(10)), Num(13))), Add(Num(13), Mod(Add(Sub(i, Num(13)), Num(3)), Num(13)))))), ("i", Nat()))),
                "The arithmetic neighbor list uses residues modulo thirteen and the same two-layer bit convention.",
                DescribeRole.Definition),
            Node("fort-test", "Finite fort predicate", "fortOK",
                Disp(Q(Iff(Eq(Call("fortOK", m), True()), And(Lt(Num(0), m), Lt(m, Pow(Num(2), Num(26))), Q(Imp(Lt(i, Num(26)), Or(Eq(Call("testBit", m, i), True()), Ne(Call("countP", Call("neighborCodes13", i), Lambda("j", Nat(), Call("testBit", m, j))), Num(1)))), ("i", Nat())))), ("m", Nat()))),
                "A valid mask is nonzero and below two to the twenty-sixth power. Every absent vertex has a number of neighbors in the mask different from one.",
                DescribeRole.Definition),
            Node("disjoint-test", "Disjoint vertex masks", "disjointOK",
                Disp(Q(Iff(Eq(Call("disjointOK", s, f), True()), And(Lt(s, Pow(Num(2), Num(26))), Lt(f, Pow(Num(2), Num(26))), Eq(Call("bitwise", Name("and"), s, f), Num(0)))), ("s", Nat()), ("f", Nat()))),
                "Both masks fit in twenty-six bits and their bitwise intersection is zero.",
                DescribeRole.Definition),
            Node("row-test", "Candidate and fort pair", "rowOK",
                Disp(Q(Iff(Eq(Call("rowOK", row), True()), And(Eq(Call("fortOK", Second(row)), True()), Eq(Call("disjointOK", First(row), Second(row)), True()))), ("row", rowType))),
                "A row pairs a candidate mask with a valid fort mask disjoint from it.",
                DescribeRole.Definition),
            Node("bit-count", "Population of the low bits", "bitCount26",
                Disp(Q(Eq(Call("bitCount26", m), Card(SetOf("i", Nat(), And(Lt(i, Num(26)), Eq(Call("testBit", m, i), True()))))), ("m", Nat()))),
                "Count the set bits at positions zero through twenty-five.",
                DescribeRole.Definition),
            Node("anchor-type", "Six oriented first forces", "Anchor13",
                Disp(Eq(Call("univ", Name("Anchor13")), anchors)),
                "The constructors distinguish an outer or inner source and a spoke, forward, or backward target.",
                DescribeRole.Definition),
            Node("finite-anchors", "Finite enumeration of the anchors", "instFintypeAnchor13",
                Disp(Eq(Call("elems", Name("instFintypeAnchor13")), anchors)),
                "The finite-type structure enumerates exactly the six constructors of Anchor13.",
                DescribeRole.Definition),
            Node("anchor-list", "The list of anchors", "anchors13",
                Disp(Eq(Name("anchors13"), ListOf(Name("outerSpoke"), Name("outerNext"), Name("outerPrev"), Name("innerSpoke"), Name("innerNext"), Name("innerPrev")))),
                "The list contains the six oriented first-force anchors in the displayed order.",
                DescribeRole.Definition),
            Node("anchor-required", "Three required black vertices", "anchorRequired",
                Disp(And(Eq(Call("anchorRequired", Name("outerSpoke")), Set(Pair(False(), Num(12)), Pair(False(), Num(0)), Pair(False(), Num(1)))),
                    Eq(Call("anchorRequired", Name("outerNext")), Set(Pair(False(), Num(12)), Pair(False(), Num(0)), Pair(True(), Num(0)))),
                    Eq(Call("anchorRequired", Name("outerPrev")), Set(Pair(False(), Num(1)), Pair(False(), Num(0)), Pair(True(), Num(0)))),
                    Eq(Call("anchorRequired", Name("innerSpoke")), Set(Pair(True(), Num(10)), Pair(True(), Num(0)), Pair(True(), Num(3)))),
                    Eq(Call("anchorRequired", Name("innerNext")), Set(Pair(True(), Num(10)), Pair(True(), Num(0)), Pair(False(), Num(0)))),
                    Eq(Call("anchorRequired", Name("innerPrev")), Set(Pair(True(), Num(3)), Pair(True(), Num(0)), Pair(False(), Num(0)))))),
                "For each anchor, the required vertices are the source at column zero and its two neighbors other than the target.",
                DescribeRole.Definition),
            Node("anchor-target", "The white target", "anchorTarget",
                Disp(And(Eq(Call("anchorTarget", Name("outerSpoke")), Pair(True(), Num(0))),
                    Eq(Call("anchorTarget", Name("outerNext")), Pair(False(), Num(1))),
                    Eq(Call("anchorTarget", Name("outerPrev")), Pair(False(), Num(12))),
                    Eq(Call("anchorTarget", Name("innerSpoke")), Pair(False(), Num(0))),
                    Eq(Call("anchorTarget", Name("innerNext")), Pair(True(), Num(3))),
                    Eq(Call("anchorTarget", Name("innerPrev")), Pair(True(), Num(10))))),
                "The target is the remaining neighbor in the oriented force, with all column indices taken modulo thirteen.",
                DescribeRole.Definition),
            Node("candidate-shape", "Seven vertices extending an anchor", "candidateShapeOK",
                Disp(Q(Iff(Eq(Call("candidateShapeOK", a, m), True()), And(Lt(m, Pow(Num(2), Num(26))), Eq(Call("bitCount26", m), Num(7)), Q(Imp(Mem(v, Call("anchorRequired", a)), Eq(Call("testBit", m, Call("code13", v)), True())), ("v", vertex)), Not(Eq(Call("testBit", m, Call("code13", Call("anchorTarget", a))), True())))), ("a", Name("Anchor13")), ("m", Nat()))),
                "A candidate has seven vertices, contains the three required vertices, and omits the white target.",
                DescribeRole.Definition),
            Node("strict-keys", "Increasing candidate masks", "StrictKeys",
                Disp(Q(Iff(Eq(Call("StrictKeys", rows), True()), Q(Imp(Lt(Add(i, Num(1)), Len(rows)), Lt(First(At(rows, i)), First(At(rows, Add(i, Num(1)))))), ("i", Nat()))), ("rows", List(rowType)))),
                "Successive row keys are strictly increasing.",
                DescribeRole.Definition),
            Node("family-order", "Size and order of an anchor family", "familyOrderOK",
                Disp(Q(Iff(Eq(Call("familyOrderOK", rows), True()), And(Eq(Len(rows), Num(7315)), Eq(Call("StrictKeys", rows), True()))), ("rows", List(rowType)))),
                "An ordered family has 7315 rows and strictly increasing candidate masks.",
                DescribeRole.Definition),
            Node("chunk-block", "Consecutive chunks of rows", "chunkBlockOK",
                Disp(Q(Iff(Eq(Call("chunkBlockOK", a, chunks, start, len), True()), Q(Imp(Lt(j, len), Q(Imp(Mem(row, Call("getD", chunks, Add(start, j), ListOf())), And(Eq(Call("candidateShapeOK", a, First(row)), True()), Eq(Call("rowOK", row), True()))), ("row", rowType))), ("j", Nat()))), ("a", Name("Anchor13")), ("chunks", List(List(rowType))), ("start", Nat()), ("len", Nat()))),
                "Every row in the selected consecutive chunks has the specified anchor shape and a disjoint fort. A chunk index beyond the list denotes the empty list.",
                DescribeRole.Definition)),
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
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Not(Formula value) => new Formula.Not(value);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Pow(Formula value, Formula power) => new Formula.Power(value, power);
    private static Formula Mod(Formula value, Formula modulus) => new Formula.Modulo(value, modulus);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Len(Formula value) => Call("length", value);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Vertices(Formula n) => Seq(Name("Bool"), Times, Sp, Fin(n));
    private static Formula List(Formula value) => Call("List", value);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula First(Formula value) => Call("fst", value);
    private static Formula Second(Formula value) => Call("snd", value);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula At(Formula value, Formula index) => Seq(value, OpenBracket, index, CloseBracket);
    private static Formula Set(params Formula[] values) => new Formula.SetLiteral([.. values]);
    private static Formula ListOf(params Formula[] values) =>
        Seq(OpenBracket, Seq([.. values.SelectMany((value, index) => index == 0
            ? new[] { value } : new[] { Comma, Sp, value })]), CloseBracket);
    private static Formula SetOf(string variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, Sp, V(variable), Sp, InMacro, Sp, domain, Bar, Sp, predicate, CloseBrace, Sp);
    private static Formula Lambda(string variable, Formula domain, Formula body) =>
        Seq(Open, LambdaLower, Sp, V(variable), Colon, domain, Comma, Sp, body, Close);
    private static Formula If(Formula condition, Formula yes, Formula no) => Call("if", condition, yes, no);
    private static Formula True() => Name("true");
    private static Formula False() => Name("false");
}
