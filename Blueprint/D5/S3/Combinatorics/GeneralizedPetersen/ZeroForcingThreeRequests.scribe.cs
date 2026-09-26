using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GeneralizedPetersen;

internal sealed class ZeroForcingThreeRequestsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThreeRequests.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/krishnan2026correction");

    public DocumentDefinition Create()
    {
        var n = V("n"); var x = V("X"); var support = V("C"); var i = V("i");
        var c = V("c"); var h = V("h"); var j = V("j"); var k = V("k");
        var d = V("d"); var sums = V("sums"); var y = V("Y"); var v = V("v");
        var occupied = Call("occupiedVertices", x);
        var positive = Call("positiveRequests", n, x);
        var negative = Call("negativeRequests", n, x);
        var word = Call("gapWord", support);
        var setVariables = new (string Name, Formula Domain)[]
            { ("n", Nat()), ("X", Fs(Vertices(n))) };
        var columnVariables = new (string Name, Formula Domain)[]
            { ("n", Nat()), ("C", Fs(Fin(n))) };
        var wordVariables = new (string Name, Formula Domain)[]
            { ("c", Nat()), ("h", Arrow(Fin(c), Nat())), ("i", Fin(c)) };
        var hits3 = Ex("k", Nat(), And(Le(Num(1), k), Le(k, c),
            Eq(Call("sums", h, i, k), Num(3))));
        var hits6 = Ex("k", Nat(), And(Le(Num(1), k), Le(k, c),
            Eq(Call("sums", h, i, k), Num(6))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The external boundary is counted by requests and collisions, whose total is dominated by ten cyclic layer scores.",
            H("Requests, Collisions, and Cyclic Gap Scores"),
            Blocks(
            Node("positive-requests", "Forward requests", "positiveRequests",
                Disp(Q(Imp(Lt(Num(0), n), Eq(positive, Image(x, "v", Call("positiveShift", n, v)))), setVariables)),
                "Each selected vertex requests its forward neighbor in the same layer.",
                DescribeRole.Definition),
            Node("negative-requests", "Backward requests", "negativeRequests",
                Disp(Q(Imp(Lt(Num(0), n), Eq(negative, Image(x, "v", Call("negativeShift", n, v)))), setVariables)),
                "Each selected vertex requests its backward neighbor in the same layer.",
                DescribeRole.Definition),
            Node("occupied-requests", "Requests landing in occupied columns", "I",
                Disp(Q(Imp(Lt(Num(0), n), Eq(Call("I", n, x), Add(Card(Inter(positive, occupied)), Card(Inter(negative, occupied))))), setVariables)),
                "Count requests into occupied columns separately in the two directions, retaining multiplicity when both directions reach the same vertex.",
                DescribeRole.Definition),
            Node("empty-collisions", "Two requests at an empty column", "K",
                Disp(Q(Imp(Lt(Num(0), n), Eq(Call("K", n, x), Card(Inter(Diff(positive, occupied), Diff(negative, occupied))))), setVariables)),
                "A collision is a vertex in an unoccupied column requested from both directions.",
                DescribeRole.Definition),
            Node("boundary-identity", "Boundary, requests, and collisions", "boundary_request_identity",
                Disp(Q(Imp(Le(Num(14), n), Eq(Add(Add(Card(Call("externalBoundary", n, x)), Call("I", n, x)), Call("K", n, x)), Add(Mul(Num(2), Card(Call("columns", x))), Card(x)))), setVariables)),
                "For every selected set at circumference at least fourteen, the boundary size plus the occupied requests and empty collisions equals twice the number of occupied columns plus the set size.",
                DescribeRole.Theorem),
            Node("sorted-columns", "Increasing enumeration of the support", "sortedColumn",
                Disp(Q(Eq(Call("sortedColumn", support), Call("orderEmbOfFin", support)), columnVariables)),
                "The support is enumerated in increasing order by Fin of its cardinality.",
                DescribeRole.Definition),
            Node("extended-column", "The terminal circumference", "extendedColumn",
                Disp(Q(Eq(Call("extendedColumn", support, j), If(Lt(j, Card(support)), Val(At(Call("sortedColumn", support), j)), n)), [.. columnVariables, ("j", Nat())])),
                "At an index below the support size, take the corresponding sorted column value; at every later index, take n.",
                DescribeRole.Definition),
            Node("gap-word", "Positive cyclic differences", "gapWord",
                Disp(Q(Eq(Call("gapWord", support, i), Add(Sub(Call("extendedColumn", support, Add(Val(i), Num(1))), Call("extendedColumn", support, Val(i))), If(Eq(Add(Val(i), Num(1)), Card(support)), Call("extendedColumn", support, Num(0)), Num(0)))), [.. columnVariables, ("i", Fin(Card(support)))])),
                "Consecutive sorted columns give the ordinary gaps; the final entry includes the wrap from the last occupied column to the first.",
                DescribeRole.Definition),
            Node("phi", "One outer-gap contribution", "phi",
                Disp(Q(Eq(Call("phi", h), If(Eq(h, Num(1)), Num(2), If(Eq(h, Num(2)), Num(1), Num(0)))), ("h", Nat()))),
                "A gap of one contributes two, a gap of two contributes one, and every other gap contributes zero.",
                DescribeRole.Definition),
            Node("cyclic-index", "Cyclic displacement of an index", "cyclicIndex",
                Disp(Q(Eq(Val(Call("cyclicIndex", i, j)), Mod(Add(Val(i), j), c)), ("c", Nat()), ("i", Fin(c)), ("j", Nat()))),
                "Add j to the index and reduce modulo the word length.",
                DescribeRole.Definition),
            Node("positive-prefix", "Forward cyclic prefix sum", "positivePrefix",
                Disp(Q(Eq(Call("positivePrefix", h, i, k), SumOver("j", Call("range", k), Call("h", Call("cyclicIndex", i, j)))), [.. wordVariables, ("k", Nat())])),
                "Sum k gaps starting with the gap at i and proceeding forward.",
                DescribeRole.Definition),
            Node("negative-prefix", "Backward cyclic prefix sum", "negativePrefix",
                Disp(Q(Eq(Call("negativePrefix", h, i, k), SumOver("j", Call("range", k), Call("h", Call("cyclicIndex", i, Sub(c, Add(j, Num(1))))))), [.. wordVariables, ("k", Nat())])),
                "The reverse scan uses the displacement c - (j + 1). This subtraction is in the natural numbers and is truncated at zero.",
                DescribeRole.Definition),
            Node("prefix-score", "Score of a directional prefix scan", "prefixScore",
                Disp(Q(Eq(Call("prefixScore", h, i, sums), If(hits3, Num(2), If(hits6, Num(1), Num(0)))), [.. wordVariables, ("sums", Arrow(Arrow(Fin(c), Nat()), Arrow(Fin(c), Arrow(Nat(), Nat()))))])),
                "A prefix of one through c gaps summing to three scores two. If none exists, a prefix summing to six scores one; otherwise the score is zero.",
                DescribeRole.Definition),
            Node("outer-score", "The outer layer slot", "A",
                Disp(Q(Eq(Call("A", h, i), Add(Call("phi", Call("h", Call("cyclicIndex", i, Sub(c, Num(1))))), Call("phi", Call("h", i)))), wordVariables)),
                "The outer slot adds the contributions from the gaps immediately before and after its column.",
                DescribeRole.Definition),
            Node("inner-score", "The inner layer slot", "B",
                Disp(Q(Eq(Call("B", h, i), Add(Call("prefixScore", h, i, Name("positivePrefix")), Call("prefixScore", h, i, Name("negativePrefix")))), wordVariables)),
                "The inner slot adds the two directional prefix scores.",
                DescribeRole.Definition),
            Node("top-ten", "The supremum of ten selected slots", "T",
                Disp(Q(Eq(Call("T", h), Call("sup", Call("powersetCard", Call("univ", Vertices(c)), Num(10)), Lambda("Y", Fs(Vertices(c)), SumOver("v", y, If(Eq(First(v), True()), Call("B", h, Second(v)), Call("A", h, Second(v))))))), ("c", Nat()), ("h", Arrow(Fin(c), Nat())))),
                "Take the supremum of the sums over all sets of ten layer-column slots. When fewer than ten slots exist, the family is empty and the natural-number supremum is zero.",
                DescribeRole.Definition),
            Node("lifted-column", "Unwrapped support coordinates", "liftedColumn",
                Disp(Q(Eq(Call("liftedColumn", support, i, k), If(Lt(Add(Val(i), k), Card(support)), Call("extendedColumn", support, Add(Val(i), k)), Add(n, Call("extendedColumn", support, Sub(Add(Val(i), k), Card(support)))))), [.. columnVariables, ("i", Fin(Card(support))), ("k", Nat())])),
                "The coordinate continues beyond one wrap by adding n after the index reaches the support size.",
                DescribeRole.Definition),
            Node("prefix-lift", "A prefix is an unwrapped displacement", "positivePrefix_lifted",
                Disp(Q(Imp(Le(k, Card(support)), Eq(Call("positivePrefix", word, i, k), Sub(Call("liftedColumn", support, i, k), Call("liftedColumn", support, i, Num(0))))), [.. columnVariables, ("i", Fin(Card(support))), ("k", Nat())])),
                "A prefix of at most one full cycle equals the difference of the corresponding lifted support coordinates.",
                DescribeRole.Theorem),
            Node("request-prefix", "An occupied endpoint determines a prefix", "positive_request_prefix",
                Disp(Q(Imp(And(Lt(Num(0), n), Lt(Num(0), d), Lt(d, n), Mem(Add(Call("sortedColumn", support, i), Call("ofNat", n, d)), support)), Ex("k", Nat(), And(Le(Num(1), k), Le(k, Card(support)), Eq(Call("positivePrefix", word, i, k), d)))), [.. columnVariables, ("i", Fin(Card(support))), ("d", Nat())])),
                "If a positive displacement less than n reaches another occupied column, that displacement is the sum of a nonempty cyclic gap prefix.",
                DescribeRole.Theorem),
            Node("prefix-endpoint", "A short prefix determines its endpoint", "positivePrefix_endpoint",
                Disp(Q(Imp(And(Lt(Num(0), n), Le(Num(1), k), Le(k, Card(support)), Lt(d, n), Eq(Call("positivePrefix", word, i, k), d)), Eq(Call("sortedColumn", support, Call("cyclicIndex", i, k)), Add(Call("sortedColumn", support, i), Call("ofNat", n, d)))), [.. columnVariables, ("i", Fin(Card(support))), ("k", Nat()), ("d", Nat())])),
                "A nonempty prefix of at most one cycle, with total below n, ends at the column obtained by adding that total modulo n.",
                DescribeRole.Theorem),
            Node("slot-domination", "Ten slots dominate requests and collisions", "slot_domination",
                Disp(Q(Imp(And(Le(Num(14), n), Eq(Card(x), Num(10))), Le(Mul(Num(2), Add(Call("I", n, x), Call("K", n, x))), Call("T", Call("gapWord", Call("columns", x))))), setVariables)),
                "For a ten-vertex set at circumference at least fourteen, twice the sum of occupied requests and empty collisions is at most the ten-slot score of its gap word.",
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
    private static Formula Mod(Formula value, Formula modulus) => new Formula.Modulo(value, modulus);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Fin(Formula value) => Call("Fin", value);
    private static Formula Vertices(Formula n) => Seq(Name("Bool"), Times, Sp, Fin(n));
    private static Formula Fs(Formula value) => Call("Finset", value);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula First(Formula value) => Call("fst", value);
    private static Formula Second(Formula value) => Call("snd", value);
    private static Formula Val(Formula value) => Call("val", value);
    private static Formula At(Formula value, Formula index) => Seq(value, OpenBracket, index, CloseBracket);
    private static Formula Image(Formula set, string variable, Formula value) =>
        new Formula.SetBuilder(value, V(variable), set);
    private static Formula SumOver(string variable, Formula domain, Formula body) =>
        Seq(Sum, Sp, Underscore, Grp(V(variable), Sp, InMacro, Sp, domain), body);
    private static Formula Lambda(string variable, Formula domain, Formula body) =>
        Seq(Open, LambdaLower, Sp, V(variable), Colon, domain, Comma, Sp, body, Close);
    private static Formula Inter(Formula left, Formula right) => Call("inter", left, right);
    private static Formula Diff(Formula left, Formula right) => Seq(Open, left, Sp, Setminus, Sp, right, Close);
    private static Formula If(Formula condition, Formula yes, Formula no) => Call("if", condition, yes, no);
    private static Formula True() => Name("true");
}
