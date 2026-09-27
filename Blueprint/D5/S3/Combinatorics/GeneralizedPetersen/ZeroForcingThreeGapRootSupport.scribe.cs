using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeGapRootSupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeGapRootSupport.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var n = V("n"); var support = V("C"); var r = V("r"); var i = V("i");
        var c = V("c"); var h = V("h"); var e = V("e"); var p = V("p");
        var positions = V("positions"); var x = V("X"); var j = V("j");
        var rootWord = Call("rotateWord", Call("gapWord", support), r);
        var wordMatches = Q(Imp(Lt(Val(i), Len(e)), Eq(Call("h", i), At(e, Val(i)))), ("i", Fin(c)));
        var canonical = ListOf(Name("positions6"), Name("positions7a"), Name("positions7b"), Name("positions8"));
        var allSupports = ListOf(Name("positions6"), Name("positions7r"), Name("positions7a"),
            Name("positions7b"), Name("positions8r"), Name("positions8"));
        var supportVariables = new (string Name, Formula Domain)[]
            { ("n", Nat()), ("C", Fs(Fin(n))), ("r", Fin(Card(support))) };
        return DocumentDefinition.Create(ScribeNode.Create(
            "Gap prefixes recover the support, and the six exceptional roots reduce to four fourteen-column supports up to reflection.",
            H("From Exceptional Gap Words to Layer Supports"),
            Blocks(
            Node("support-from-gaps", "Translated columns are gap-prefix positions", "support_from_gaps",
                Disp(Q(Imp(Lt(Num(0), n), Eq(Image(support, "x", Sub(x, Call("sortedColumn", support, r))), Image(Fin(Card(support)), "i", Call("ofNat", n, Call("positivePrefix", rootWord, Num(0), Val(i)))))), supportVariables)),
                "Translate the chosen root column to zero. Every occupied column is then a prefix sum of the rotated gap word, reduced modulo the circumference.",
                DescribeRole.Theorem),
            Node("bounded-exception", "Classify a bounded word above the threshold", "bounded_gap_exception",
                Disp(Q(Imp(And(Le(Num(5), c), Le(c, Num(8)), Q(And(Le(Num(1), Call("h", i)), Le(Call("h", i), Num(7))), ("i", Fin(c))), Le(Num(14), SumOver("i", Fin(c), Call("h", i))), Le(Add(Mul(Num(4), c), Num(6)), Call("T", h))), Ex("r", Fin(c), Ex("e", List(Nat()), And(Mem(e, Name("exceptionalRoots")), Eq(Len(e), c), Q(Imp(Lt(Val(i), Len(e)), Eq(Call("rotateWord", h, r, i), At(e, Val(i)))), ("i", Fin(c))))))), ("c", Nat()), ("h", Arrow(Fin(c), Nat())))),
                "A word of five through eight gaps, each between one and seven, with total at least fourteen and score above the parity threshold rotates to an exceptional root.",
                DescribeRole.Theorem),
            Node("layer-digit", "The layer state of one column", "layerDigit",
                Disp(Q(Eq(Call("layerDigit", x, p), If(Mem(Pair(False(), p), x), If(Mem(Pair(True(), p), x), Num(2), Num(0)), Num(1))), ("X", Fs(Vertices(Num(14)))), ("p", Fin(Num(14))))),
                "An outer-only column has digit zero, an inner-only column has digit one, and a column with both vertices has digit two. A column without an outer vertex is assigned one, including an empty column.",
                DescribeRole.Definition),
            Node("layer-digits", "The list of layer states", "layerDigits",
                Disp(Q(Eq(Call("layerDigits", positions, x), Call("ofFn", Lambda("j", Fin(Len(positions)), Call("layerDigit", x, Call("ofNat", Num(14), At(positions, Val(j))))))), ("positions", List(Nat())), ("X", Fs(Vertices(Num(14)))))),
                "Read the layer state at every listed support position, interpreting its index modulo fourteen.",
                DescribeRole.Definition),
            Node("layer-code", "Encode the support labels", "layerCode",
                Disp(Q(Eq(Call("layerCode", positions, x), Call("ofDigits", Num(3), Call("layerDigits", positions, x))), ("positions", List(Nat())), ("X", Fs(Vertices(Num(14)))))),
                "The list of layer digits is encoded as a natural number in base three, with its first digit least significant.",
                DescribeRole.Definition),
            Node("support-set", "The columns in a position list", "supportSet",
                Disp(Q(Eq(Call("supportSet", positions), Image(Fin(Len(positions)), "j", Call("ofNat", Num(14), At(positions, Val(j))))), ("positions", List(Nat())) )),
                "Take the finite set of listed positions after reduction modulo fourteen.",
                DescribeRole.Definition),
            Node("recover-labels", "Decoding the layer code recovers the set", "labelledSupport_layerCode",
                Disp(Q(Imp(And(Q(Lt(At(positions, Val(j)), Num(14)), ("j", Fin(Len(positions)))), Eq(Call("columns", x), Call("supportSet", positions))), Eq(Call("labelledSupport", positions, Call("layerCode", positions, x)), x)), ("positions", List(Nat())), ("X", Fs(Vertices(Num(14)))))),
                "Every set whose occupied columns are exactly the listed positions is recovered by its layer code, provided all listed positions are below fourteen. No assumption on the number of selected vertices is needed.",
                DescribeRole.Theorem),
            Node("direct-score-identity", "The direct scan equals requests plus collisions", "directScore_eq",
                Disp(Q(Eq(Call("directScore", x), Add(Call("I", Num(14), x), Call("K", Num(14), x))), ("X", Fs(Vertices(Num(14)))))),
                "The direct source and destination counts agree with the semantic occupied-request and empty-collision counts.",
                DescribeRole.Theorem),
            Node("canonical-supports", "Sizes and reflections of the support lists", "canonical_support_facts",
                Disp(And(Q(Imp(Mem(p, canonical), And(Q(Lt(At(p, Val(j)), Num(14)), ("j", Fin(Len(p)))), Eq(Card(Call("supportSet", p)), Len(p)))), ("p", List(Nat()))), Eq(Image(Call("supportSet", Name("positions7r")), "i", Sub(Num(3), i)), Call("supportSet", Name("positions7a"))), Eq(Image(Call("supportSet", Name("positions8r")), "i", Sub(Num(3), i)), Call("supportSet", Name("positions8"))))),
                "The four canonical lists have distinct positions below fourteen. Reflection i to three minus i in Fin 14 sends positions7r to positions7a and positions8r to positions8.",
                DescribeRole.Theorem),
            Node("exceptional-circumference", "Every exceptional support has circumference fourteen", "exceptionalRoot_circumference",
                Disp(Q(Imp(And(Lt(Num(0), n), Mem(e, Name("exceptionalRoots")), Eq(Len(e), Card(support)), Q(Imp(Lt(Val(i), Len(e)), Eq(Call("rotateWord", Call("gapWord", support), r, i), At(e, Val(i)))), ("i", Fin(Card(support))))), Eq(n, Num(14))), [.. supportVariables, ("e", List(Nat()))])),
                "An exceptional root matching a rotated support word has total equal to the circumference, so that circumference is fourteen.",
                DescribeRole.Theorem),
            Node("word-support", "Positions determined by gap prefixes", "wordSupport",
                Disp(Q(Imp(Lt(Num(0), c), Eq(Call("wordSupport", h), Image(Fin(c), "i", Call("ofNat", Num(14), Call("positivePrefix", h, Num(0), Val(i)))))), ("c", Nat()), ("h", Arrow(Fin(c), Nat())))),
                "The word support consists of the prefix positions starting at zero, reduced modulo fourteen.",
                DescribeRole.Definition),
            Node("exceptional-support", "The six possible exceptional supports", "exceptionalRoot_support",
                Disp(Q(Imp(And(Lt(Num(0), c), Mem(e, Name("exceptionalRoots")), Eq(Len(e), c), wordMatches), Ex("p", List(Nat()), And(Mem(p, allSupports), Eq(Call("wordSupport", h), Call("supportSet", p))))), ("c", Nat()), ("h", Arrow(Fin(c), Nat())), ("e", List(Nat())))),
                "A word agreeing with one of the six exceptional roots yields one of the six displayed support lists, including the two reflected variants.",
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
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
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
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Len(Formula value) => Call("length", value);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Vertices(Formula n) => Seq(Name("Bool"), Times, Sp, Fin(n));
    private static Formula Fs(Formula value) => Call("Finset", value);
    private static Formula List(Formula value) => Call("List", value);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula Pair(Formula left, Formula right) => Seq(Open, left, Comma, Sp, right, Close);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula At(Formula value, Formula index) => Seq(value, OpenBracket, index, CloseBracket);
    private static Formula ListOf(params Formula[] values) =>
        Seq(OpenBracket, Seq([.. values.SelectMany((value, index) => index == 0
            ? new[] { value } : new[] { Comma, Sp, value })]), CloseBracket);
    private static Formula Image(Formula set, string variable, Formula value) =>
        new Formula.SetBuilder(value, V(variable), set);
    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(V(variable), Sp, InMacro, Sp, domain), body);
    private static Formula Lambda(string variable, Formula domain, Formula body) =>
        Seq(Open, LambdaLower, Sp, V(variable), Colon, domain, Comma, Sp, body, Close);
    private static Formula If(Formula condition, Formula yes, Formula no) => Call("if", condition, yes, no);
    private static Formula True() => Name("true");
    private static Formula False() => Name("false");
}
