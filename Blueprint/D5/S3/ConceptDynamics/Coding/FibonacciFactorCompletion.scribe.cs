using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class FibonacciFactorCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula I(string name) => F.Id(name);
    private static Formula Returns => Call("List", I("Return"));
    private static Formula Add(Formula a, Formula b) => Call("add", a, b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract", a, b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Pow(Formula a, Formula b) => Call("power", a, b);

    private static Formula BoundaryGeometry()
    {
        var model = I("model"); var xs = I("execution"); var j = I("j");
        var p = I("p"); var n = I("n"); var k = I("k");
        Formula State(Formula side) => Call("execute", side, Call("take", xs, p),
            Call("initial", side, model));
        Formula Internal(Formula side) => Sub(Call("hSide", side),
            Mul(Pow(I("rho"), k), Sub(Call("hSide", side), Mul(Pow(I("chi"), n), State(side)))));
        var z = Internal(j);
        var signed = Add(I("c0"), Mul(Call("sign", j), z));
        return Disp(All(And(
            All(And(Call("lt", Call("aSide", j), State(j)), Call("lt", State(j), Call("hSide", j))),
                B("j", I("Side")), B("p", I("Nat"))),
            All(Call("lt", State(I("high")), State(I("low"))), B("p", I("Nat"))),
            All(And(Call("lt", D(0), z), Call("lt", z, Call("hSide", j)),
                Call("le", D(0), signed), Call("le", signed, I("T2"))),
                B("j", I("Side")), B("p", I("Nat")), B("n", I("Nat")), B("k", I("Nat"))),
            All(Call("lt", Internal(I("high")), Internal(I("low"))),
                B("p", I("Nat")), B("n", I("Nat")), B("k", I("Nat"))),
            All(Equal(Call("coordinate", Call("sourcePrefix", j, model, xs),
                    Add(Call("length", Call("stem", j)), Call("listWeight", Call("drop", xs, p)))),
                Add(I("c0"), Mul(Call("sign", j), State(j)))),
                B("j", I("Side")), B("p", I("Nat")))) ,
            B("model", I("Model")), B("execution", Returns)));
    }

    private static Formula StrictRecordSupply()
    {
        var model = I("model"); var o = I("o"); var b = I("b");
        var xs = I("execution"); var k = I("K"); var high = I("high");
        var h = Call("hSide", high); var a = Call("aSide", high);
        var ck = Pow(I("chi"), k); var g2 = Pow(I("g"), D(2));
        var z = Call("divide", a, Sub(D(1), Mul(I("rho"), ck)));
        var q = Sub(I("lam"), Mul(Mul(g2, ck), h));
        var psi = Sub(I("lam"), Mul(Mul(g2, ck), z));
        var d = Call("divide", Call("divide", Sub(I("lam"), b), g2), ck);
        var trace = Call("GuardTrace", k, d, I("true"), high, xs,
            Call("initial", high, model));
        Formula Supply(string contract) => Call("ActualPairSupply", model, o, b, I(contract), xs);
        Formula Iff(Formula x, Formula y) => And(
            new Formula.Logic(x, FormulaLogicOperator.Implies, y),
            new Formula.Logic(y, FormulaLogicOperator.Implies, x));
        return Disp(All(new Formula.Logic(
            And(Call("le", D(2), k), Call("lt", q, b), Call("lt", b, psi)),
            FormulaLogicOperator.Implies,
            And(Iff(Supply("strict"), trace), Iff(Supply("recordMargin"), trace))),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("execution", Returns), B("K", I("Nat"))));
    }

    private static Formula ClosedRecordSupply()
    {
        var model = I("model"); var o = I("o"); var b = I("b");
        var xs = I("execution"); var k = I("K"); var high = I("high");
        var h = Call("hSide", high); var a = Call("aSide", high);
        var ck = Pow(I("chi"), k); var g2 = Pow(I("g"), D(2));
        var z = Call("divide", a, Sub(D(1), Mul(I("rho"), ck)));
        var q = Sub(I("lam"), Mul(Mul(g2, ck), h));
        var psi = Sub(I("lam"), Mul(Mul(g2, ck), z));
        var d = Call("divide", Call("divide", Sub(I("lam"), b), g2), ck);
        var trace = Call("GuardTrace", k, d, Call("boolNot", Call("apply", o, D(0))), high, xs,
            Call("initial", high, model));
        Formula Supply(string contract) => Call("ActualPairSupply", model, o, b, I(contract), xs);
        Formula Iff(Formula x, Formula y) => And(
            new Formula.Logic(x, FormulaLogicOperator.Implies, y),
            new Formula.Logic(y, FormulaLogicOperator.Implies, x));
        return Disp(All(new Formula.Logic(
            And(Call("le", D(2), k), Call("lt", q, b), Call("lt", b, psi)),
            FormulaLogicOperator.Implies,
            Iff(Supply("closed"), trace)),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("execution", Returns), B("K", I("Nat"))));
    }

    private static Formula ResetFirstReturn()
    {
        var o = I("o"); var b = I("b"); var k = I("K"); var high = I("high");
        var reset = I("R"); var rm = Call("m", reset); var xs = I("xs");
        var h = Call("hSide", high); var a = Call("aSide", high);
        var ck = Pow(I("chi"), k); var g2 = Pow(I("g"), D(2));
        var d = Call("divide", Call("divide", Sub(I("lam"), b), g2), ck);
        var q = Sub(I("lam"), Mul(Mul(g2, ck), h));
        var psi = Sub(I("lam"), Mul(Mul(g2, ck),
            Call("divide", a, Sub(D(1), Mul(I("rho"), ck)))));
        var bound = Sub(h, Mul(Pow(I("rho"), rm), Sub(h, Mul(I("chi"), a))));
        Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
        Formula Output(Formula z) => Call("returnMap", high, reset, z);
        var z = I("z"); var m = I("m"); var r = I("r"); var state = I("D");
        var difference = Sub(Sub(h, Mul(Pow(I("rho"), Add(m, D(1))),
                Sub(h, Mul(Pow(I("chi"), r), z)))),
            Sub(h, Mul(Pow(I("rho"), m), Sub(h, Mul(Pow(I("chi"), r), h)))));
        var brace = Add(Sub(a, Mul(Pow(I("chi"), r), h)),
            Mul(Mul(I("rho"), Pow(I("chi"), r)), z));
        var source = I("sourceModel"); var target = I("targetModel");
        var cons = Call("cons", reset, xs);
        var conclusion = And(Equal(Call("r", reset), D(1)),
            Call("lt", Call("max", Call("max", Call("xSide", high), Call("ySide", high)), d), bound),
            All(Imp(Call("lt", a, state), Call("lt", bound, Output(state))), B("D", I("Real"))),
            All(Imp(Call("le", a, state), Call("le", bound, Output(state))), B("D", I("Real"))),
            All(Imp(Call("GuardTrace", k, d, I("false"), high, xs, Call("initial", high, source)),
                Call("ActualPairSupply", target, o, b, I("strict"), cons)),
                B("sourceModel", I("Model")), B("targetModel", I("Model")), B("xs", Returns)),
            All(Equal(Call("listWeight", cons), Add(Add(D(2, 0), Mul(D(6), rm)), Call("listWeight", xs))),
                B("xs", Returns)),
            All(Imp(And(Call("le", D(1), m), Call("le", D(1), r), Call("le", r, k), Call("le", a, z)),
                And(Equal(difference, Mul(Pow(I("rho"), m), brace)), Call("lt", D(0), difference))),
                B("m", I("Nat")), B("r", I("Nat")), B("z", I("Real"))));
        return Disp(All(Imp(And(Call("le", D(2), k), Call("lt", q, b), Call("lt", b, psi)),
            new Formula.BindMany(FormulaQuantifier.Exists, [B("R", I("Return"))], conclusion)),
            B("o", I("Ownership")), B("b", I("Real")), B("K", I("Nat"))));
    }

    private static Formula CompleteParser()
    {
        var a = I("a"); var xs = I("xs"); var model = I("model");
        var word = Call("executionWord", Call("cons", a, xs));
        var r = Call("r", a); var m = Call("m", a);
        return Disp(And(
            All(Equal(Call("takeWhile", word, I("isC")), Call("replicate", r, I("c"))),
                B("a", I("Return")), B("xs", Returns)),
            All(Equal(Call("takeWhile", Call("drop", word, r), I("isU")),
                Call("replicate", m, I("u"))), B("a", I("Return")), B("xs", Returns)),
            Call("Injective", I("executionWord")),
            All(Equal(Call("wordWeight", Call("executionWord", xs)), Call("listWeight", xs)),
                B("xs", Returns)),
            All(Call("Injective", Call("history", model)), B("model", I("Model")))));
    }

    private static Formula BilateralPast()
    {
        var omega = I("omega"); var nu = I("nu"); var i = I("i"); var n = I("N");
        var x = I("x"); var y = I("y"); var z = I("z"); var k = I("k");
        var h = Call("hSide", I("high"));
        var words = new Formula.TypeArrow(I("Int"), I("CuLetter"));
        Formula State(Formula w, Formula at) => Call("pastState", w, at);
        Formula Past(Formula w, Formula seed) => Call("finitePast", w, i, n, seed);
        Formula At(Formula w, Formula at) => Call("apply", w, at);
        Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
        Formula Bounds(Formula value) => And(Call("le", D(0), value), Call("le", value, h));
        var power = Pow(I("g"), Call("pastWeight", omega, i, n));
        var previous = Sub(Sub(i, D(1)), k);
        return Disp(And(
            All(Equal(Sub(Past(omega, y), Past(omega, x)), Mul(power, Sub(y, x))),
                B("omega", words), B("i", I("Int")), B("N", I("Nat")), B("x", I("Real")), B("y", I("Real"))),
            All(And(Call("le", D(0), power), Call("le", power, Pow(I("rho"), n))),
                B("omega", words), B("i", I("Int")), B("N", I("Nat"))),
            All(Bounds(State(omega, i)), B("omega", words), B("i", I("Int"))),
            All(Imp(Bounds(z), Call("Tendsto", new Formula.Sequence(Past(omega, z), n, I("Nat")),
                I("atTop"), Call("nhds", State(omega, i)))),
                B("omega", words), B("i", I("Int")), B("z", I("Real"))),
            All(Equal(State(omega, Add(i, D(1))), Call("letterMap", At(omega, i), State(omega, i))),
                B("omega", words), B("i", I("Int"))),
            All(Imp(And(All(Bounds(At(y, i)), B("i", I("Int"))),
                All(Equal(At(y, Add(i, D(1))), Call("letterMap", At(omega, i), At(y, i))), B("i", I("Int")))),
                Equal(y, Call("pastState", omega))), B("omega", words),
                B("y", new Formula.TypeArrow(I("Int"), I("Real")))),
            All(Imp(All(Equal(At(omega, previous), At(nu, previous)), B("k", Call("Fin", n))),
                Call("le", new Formula.Absolute(Sub(State(omega, i), State(nu, i))), Mul(h, Pow(I("rho"), n)))),
                B("omega", words), B("nu", words), B("i", I("Int")), B("N", I("Nat"))),
            All(Equal(State(Call("const", I("u")), i), h), B("i", I("Int"))),
            All(Call("Continuous", new Formula.Sequence(State(omega, i), omega, words)), B("i", I("Int"))),
            All(Imp(Call("le", D(1), I("K")),
                And(Call("Nonempty", Call("AuxiliaryLanguage", I("K"), I("d"))),
                    Call("IsCompact", Call("AuxiliaryLanguage", I("K"), I("d"))))),
                B("K", I("Nat")), B("d", I("Real"))),
            All(Equal(State(Call("shift", omega, I("j")), i), State(omega, Add(i, I("j")))),
                B("omega", words), B("i", I("Int")), B("j", I("Int"))),
            All(new Formula.Logic(Call("member", omega, Call("AuxiliaryLanguage", I("K"), I("d"))),
                FormulaLogicOperator.Iff,
                Call("member", Call("shift", omega, I("j")), Call("AuxiliaryLanguage", I("K"), I("d")))),
                B("omega", words), B("j", I("Int")), B("K", I("Nat")), B("d", I("Real")))));
    }

    private static Formula LowerPadding()
    {
        var k = I("K"); var d = I("d"); var model = I("model"); var xs = I("xs");
        var p = I("p"); var word = Call("executionWord", xs);
        var omega = Call("uPadding", word); var prefix = Call("take", xs, p);
        Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
        var trace = Call("GuardTrace", k, d, I("false"), I("high"), xs,
            Call("initial", I("high"), model));
        return Disp(All(Imp(And(Call("le", D(1), k), trace), And(
            Equal(Call("pastState", omega, D(0)), Call("hSide", I("high"))),
            All(Imp(Call("le", p, Call("length", xs)), Call("lt",
                Call("execute", I("high"), prefix, Call("initial", I("high"), model)),
                Call("pastState", omega, Call("castInt", Call("length", Call("executionWord", prefix)))))),
                B("p", I("Nat"))),
            Call("member", omega, Call("AuxiliaryLanguage", k, d)),
            Call("Occurs", omega, word), Call("AuxiliaryFactor", k, d, word),
            Equal(Call("wordWeight", word), Call("listWeight", xs)))),
            B("K", I("Nat")), B("d", I("Real")), B("model", I("Model")), B("xs", Returns)));
    }

    private static Formula FiniteRunDecomposition()
    {
        var w = I("w"); var a = I("a"); var xs = I("xs");
        var ap = I("ap"); var xp = I("xp");
        var letters = Call("List", I("CuLetter"));
        Formula Rep(Formula n) => Call("replicate", n, I("u"));
        Formula Parsed(Formula n, Formula list) => Call("append", Rep(n), Call("executionWord", list));
        Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
        var ends = new Formula.Logic(Equal(w, I("nil")), FormulaLogicOperator.Or,
            Equal(Call("getLastOption", w), Call("some", I("u"))));
        var body = And(Equal(w, Parsed(a, xs)),
            All(Imp(Equal(w, Parsed(ap, xp)), And(Equal(ap, a), Equal(xp, xs))),
                B("ap", I("Nat")), B("xp", Returns)));
        return Disp(All(Imp(ends,
            new Formula.BindMany(FormulaQuantifier.Exists, [B("a", I("Nat")), B("xs", Returns)], body)),
            B("w", letters)));
    }

    private static Formula SourceAddressInjection()
    {
        var j = I("j"); var model = I("model"); var xs = I("xs"); var ys = I("ys");
        var premise = And(Equal(Call("listWeight", xs), Call("listWeight", ys)),
            Equal(Call("source", j, model, xs), Call("source", j, model, ys)));
        return Disp(All(new Formula.Logic(premise, FormulaLogicOperator.Implies, Equal(xs, ys)),
            B("j", I("Side")), B("model", I("Model")), B("xs", Returns), B("ys", Returns)));
    }

    private static Formula OccurrenceRunGuards()
    {
        var kmax = I("K"); var d = I("d"); var omega = I("omega");
        var i = I("i"); var xs = I("xs"); var k = I("k");
        var word = Call("executionWord", xs); var len = Call("length", word);
        var value = Call("getElem", word, k);
        Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
        var observed = new Formula.Logic(Call("lt", Add(Call("val", k), D(1)), len),
            FormulaLogicOperator.Or, Equal(value, I("c")));
        var letters = All(Imp(observed, Equal(Call("apply", omega, Add(i, Call("castInt", Call("val", k)))), value)),
            B("k", Call("Fin", len)));
        var premise = And(Call("le", D(1), kmax), Call("member", omega, Call("AuxiliaryLanguage", kmax, d)), letters);
        return Disp(All(Imp(premise,
            Call("GuardTrace", kmax, d, I("false"), I("high"), xs, Call("pastState", omega, i))),
            B("K", I("Nat")), B("d", I("Real")),
            B("omega", new Formula.TypeArrow(I("Int"), I("CuLetter"))),
            B("i", I("Int")), B("xs", Returns)));
    }

    private static Formula UpperCompletion()
    {
        var o = I("o"); var b = I("b"); var k = I("K"); var high = I("high");
        var reset = I("R"); var model = I("model"); var w = I("w");
        var a = I("a"); var first = I("first"); var rest = I("rest");
        var ap = I("ap"); var xp = I("xp"); var rm = Call("m", reset);
        var ck = Pow(I("chi"), k); var g2 = Pow(I("g"), D(2));
        var d = Call("divide", Call("divide", Sub(I("lam"), b), g2), ck);
        var q = Sub(I("lam"), Mul(Mul(g2, ck), Call("hSide", high)));
        var psi = Sub(I("lam"), Mul(Mul(g2, ck), Call("divide", Call("aSide", high),
            Sub(D(1), Mul(I("rho"), ck)))));
        var endsC = Equal(Call("getLastOption", w), Call("some", I("c")));
        var filled = Call("if", endsC, Call("append", w, Call("singleton", I("u"))), w);
        var originalList = Call("cons", first, rest);
        var merged = Call("Return", Add(rm, a), D(1));
        var extra = Call("Return", Add(Call("m", first), D(1)), Call("r", first));
        var completed = Call("cons", merged, Call("cons", extra, rest));
        Formula Rep(Formula n, Formula l) => Call("replicate", n, l);
        Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
        var normal = Call("cons", I("c"), Call("append", Rep(Add(rm, a), I("u")),
            Call("append", Rep(Call("r", first), I("c")),
                Call("append", Rep(Add(Call("m", first), D(1)), I("u")), Call("executionWord", rest)))));
        var body = And(Equal(filled, Call("append", Rep(a, I("u")), Call("executionWord", originalList))),
            All(Imp(Equal(filled, Call("append", Rep(ap, I("u")), Call("executionWord", xp))),
                And(Equal(ap, a), Equal(xp, originalList))), B("ap", I("Nat")), B("xp", Returns)),
            Call("ActualPairSupply", model, o, b, I("strict"), completed),
            Equal(Call("executionWord", completed), normal),
            Equal(Call("listWeight", completed), Add(Add(Call("wordWeight", w),
                Add(D(2, 0), Mul(D(6), rm))), Call("if", endsC, D(1, 2), D(6)))));
        var factors = All(Imp(And(Call("AuxiliaryFactor", k, d, w), Call("member", I("c"), w)),
            new Formula.BindMany(FormulaQuantifier.Exists,
                [B("a", I("Nat")), B("first", I("Return")), B("rest", Returns)], body)),
            B("model", I("Model")), B("w", Call("List", I("CuLetter"))));
        return Disp(All(Imp(And(Call("le", D(2), k), Call("lt", q, b), Call("lt", b, psi)),
            new Formula.BindMany(FormulaQuantifier.Exists, [B("R", I("Return"))],
                And(Equal(Call("r", reset), D(1)), factors))),
            B("o", I("Ownership")), B("b", I("Real")), B("K", I("Nat"))));
    }


    private static Formula DecoderConfigurationExtraction()
    {
        Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
        var model = I("model"); var o = I("o"); var b = I("b"); var contract = I("contract");
        var family = I("family"); var xs = I("xs"); var j = I("j"); var p = I("p");
        var a = I("a"); var r = I("record"); var n = I("n"); var x = I("coordinatePath");
        var path = I("guardPath"); var err = I("error");
        var natColor = new Formula.TypeArrow(I("Nat"), I("Color"));
        var natLabel = new Formula.TypeArrow(I("Nat"), I("Label"));
        Formula Apply(Formula f, Formula at) => Call("apply", f, at);
        Formula Hist(Formula list) => Call("history", model, list);
        Formula Run(Formula h) => Call("foldl", Call("appendOutputStep", I("advance")),
            Call("pair", I("initialConfiguration"), I("initialOutput")), h);
        Formula Out(Formula h) => Call("second", Run(h));
        Formula Front(Formula input) => Call("ofFn", Call("restrict", input, n));
        Formula Source(Formula side) => Call("source", side, model, xs);
        Formula FiniteSource(Formula address) => new Formula.BindMany(FormulaQuantifier.Exists,
            [B("M", I("Nat"))], All(Imp(Call("le", I("M"), p), Equal(Apply(address, p), I("L0"))),
                B("p", I("Nat"))));
        Formula Record(Formula address, Formula input) => new Formula.BindMany(FormulaQuantifier.Exists,
            [B("coordinatePath", new Formula.TypeArrow(I("Nat"), I("Real"))),
             B("guardPath", new Formula.TypeArrow(I("Nat"), I("Guard"))),
             B("error", new Formula.TypeArrow(I("Nat"), I("Real")))], And(
                Equal(Apply(path, D(0)), I("G0")),
                All(Equal(Call("nextGuard", Apply(path, p), Apply(address, p)),
                    Call("some", Apply(path, Add(p, D(1))))), B("p", I("Nat"))),
                All(Call("InSupport", Apply(path, p), Apply(x, p)), B("p", I("Nat"))),
                All(Equal(Apply(x, p), Call("branch", Apply(address, p), Apply(x, Add(p, D(1))))),
                    B("p", I("Nat"))),
                Call("ErrorBound", b, contract, err),
                All(Equal(Call("observe", o, Apply(x, p), Apply(err, p)), Apply(input, p)),
                    B("p", I("Nat")))));
        var output = Out(Front(r));
        var safe = All(Imp(Record(a, r), All(Imp(Call("lt", p, Call("length", output)),
            Equal(Call("get", output, p), Apply(a, p))), B("n", I("Nat")), B("p", I("Nat")))),
            B("a", natLabel), B("record", natColor));
        var live = All(Imp(And(Record(a, r), FiniteSource(a)),
            All(new Formula.BindMany(FormulaQuantifier.Exists, [B("n", I("Nat"))],
                Call("lt", p, Call("length", output))), B("p", I("Nat")))),
            B("a", natLabel), B("record", natColor));
        var supplied = All(Imp(Call("member", xs, family), And(
            Equal(Call("listWeight", xs), I("N")),
            Call("ActualPairSupply", model, o, b, contract, xs))), B("xs", Returns));
        var conclusion = And(
            All(Imp(Call("member", xs, family), All(And(
                Record(Source(j), Call("pairedRecord", model, o, xs, j)), FiniteSource(Source(j))),
                B("j", I("Side")))), B("xs", Returns)),
            All(Imp(Call("member", xs, family), Equal(Out(Hist(xs)), Call("nil", I("Label")))),
                B("xs", Returns)),
            Call("InjectiveOn", Call("runHistory", I("advance"), I("initialConfiguration"),
                I("initialOutput"), model), family),
            Call("InjectiveOn", Call("configurationHistory", I("advance"), I("initialConfiguration"),
                I("initialOutput"), model), family),
            Call("le", Call("card", family), Mul(Call("card", Call("image", family,
                Call("configurationHistory", I("advance"), I("initialConfiguration"),
                    I("initialOutput"), model))), Add(D(0), D(1)))));
        return Disp(All(Imp(And(supplied, safe, live), conclusion),
            B("Configuration", I("Type")),
            B("advance", new Formula.TypeArrow(I("Configuration"), new Formula.TypeArrow(I("Color"),
                Call("Product", I("Configuration"), Call("List", I("Label")))))),
            B("initialConfiguration", I("Configuration")), B("initialOutput", Call("List", I("Label"))),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("contract", I("Contract")), B("N", I("Nat")), B("family", Call("Finset", Returns))));
    }

    private static Formula OperationStorage()
    {
        Formula Fn(Formula a,Formula b) => Call("Function",a,b);
        Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
        Formula Ex(Formula a,params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[.. v],a);
        Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
        var c=I("Configuration");var nat=I("Nat");var action=I("action");var initial=I("initialConfiguration");
        var model=I("model");var o=I("o");var b=I("b");var contract=I("contract");var n=I("N");
        var record=Call("OperationRecord",o,b,contract);var enc=I("encoding");var cuts=I("cuts");
        var family=I("family");var x=I("x");var t=I("t");var xs=I("xs");var states=I("states");
        var xType=Call("ExactActualPairFamily",model,o,b,contract,n);
        var cut=Call("apply",cuts,x);var state=Call("state",cut);var output=Call("output",cut);
        var horizon=Add(Call("observationOffset",model),n);
        Formula Peak(Formula h) => Call("Peak",action,initial,record,enc,h);
        var cutSpec=All(And(Call("Cut",action,initial,Call("history",model,Call("val",x)),cut),
            All(Imp(Call("Cut",action,initial,Call("history",model,Call("val",x)),t),Equal(t,cut)),B("t",Call("Frame",c,I("Label")))),
            Equal(Call("acquired",cut),horizon),Equal(output,I("nil")),Call("ReachThrough",action,initial,record,horizon,state)),B("x",xType));
        var count=Call("NatCard",xType);var bound=I("B");
        var capacity=All(Imp(Call("le",Peak(horizon),Call("toWithTop",bound)),
            Call("le",count,Sub(Pow(D(2),Add(bound,D(1))),D(1)))),B("B",nat));
        var fixedCapacity=All(Imp(All(Equal(Call("length",Call("apply",enc,state)),bound),B("x",xType)),
            Call("le",count,Pow(D(2),bound))),B("B",nat));
        var stateSet=Ex(And(Equal(Call("card",states),count),All(Iff(Call("member",I("c"),states),
            Ex(Equal(Call("state",Call("apply",cuts,x)),I("c")),B("x",xType))),B("c",c))),B("states",Call("Finset",c)));
        var vertices=All(Imp(And(Call("OperationRecord",o,b,contract,I("a"),I("r")),
            Call("Trace",action,Call("full",I("r")),Call("frame",initial,D(0),I("nil")),t,I("vertices")),
            Call("le",Call("acquired",t),horizon),Call("member",I("c"),I("vertices"))),
            Call("le",Call("toWithTop",Call("length",Call("apply",enc,I("c")))),Peak(horizon))),
            B("a",Fn(nat,I("Label"))),B("r",Fn(nat,I("Color"))),B("t",Call("Frame",c,I("Label"))),
            B("vertices",Call("List",c)),B("c",c));
        var conclusion=Ex(And(All(Iff(Call("member",xs,family),And(Call("ActualPairSupply",model,o,b,contract,xs),
            Equal(Call("listWeight",xs),n))),B("xs",Returns)),Equal(Call("card",family),count),cutSpec,
            Call("Injective",Call("stateCutMap",cuts)),stateSet,capacity,fixedCapacity,
            Call("Monotone",Call("PeakFunction",action,initial,record,enc)),vertices),
            B("family",Call("Finset",Returns)),B("cuts",Fn(xType,Call("Frame",c,I("Label")))));
        var premises=And(Call("Processing",action,initial,record),Call("OperationSafety",action,initial,o,b,contract),
            Call("OperationLiveness",action,initial,o,b,contract),Call("InjOn",enc,Call("AllActualReachable",action,initial,record)));
        return Disp(All(Imp(premises,conclusion),B("Configuration",I("Type")),
            B("action",Fn(c,Call("Op",c,I("Color"),I("Label")))),B("initialConfiguration",c),B("model",I("Model")),
            B("o",I("Ownership")),B("b",I("Real")),B("contract",I("Contract")),B("N",nat),B("encoding",Fn(c,Call("List",I("Bool"))))));
    }
    private static Formula OperationStem()
    {
        Formula Fn(Formula a,Formula b) => Call("Function",a,b);
        Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
        Formula Ex(Formula a,params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists,[.. v],a);
        Formula Iff(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
        var c=I("Configuration");var zType=I("Z");var z=I("z");var nat=I("Nat");var action=I("action");var initial=I("initialConfiguration");
        var o=I("o");var b=I("b");var contract=I("contract");var n=I("n");var w=I("w");var k=Call("length",w);
        var alpha=I("alpha");var beta=I("beta");var high=I("highRecord");var low=I("lowRecord");
        Formula Source(Formula a,Formula q) => Call("apply",a,q);
        Formula At(Formula a,Formula q,Formula p) => Call("apply",Source(a,q),p);
        var actual=All(And(Call("OperationRecord",o,b,contract,Source(alpha,z),Source(high,z)),
            Call("OperationFiniteSource",Source(alpha,z)),Call("OperationRecord",o,b,contract,Source(beta,z),Source(low,z))),B("z",zType));
        var past=All(Imp(Call("lt",I("p"),n),Equal(At(high,z,I("p")),At(low,z,I("p")))),B("z",zType),B("p",nat));
        var future=All(Equal(At(high,z,Add(n,I("p"))),At(high,I("otherZ"),Add(n,I("p")))),B("z",zType),B("otherZ",zType),B("p",nat));
        var stems=All(Imp(Call("lt",I("i"),k),And(Equal(At(alpha,z,I("i")),Call("get",w,I("i"))),
            Equal(At(beta,z,I("i")),Call("get",w,I("i"))))),B("z",zType),B("i",nat));
        var difference=All(Call("notEqual",At(alpha,z,k),At(beta,z,k)),B("z",zType));
        var cuts=I("cuts");var states=I("states");var cut=Call("apply",cuts,z);var output=Call("output",cut);var state=Call("state",cut);
        var cutSpec=All(And(Call("Cut",action,initial,Call("front",Source(high,z),n),cut),Call("le",Call("length",output),k),
            Equal(output,Call("take",w,Call("length",output))),Call("IsPrefix",output,w)),B("z",zType));
        var membership=All(Iff(Call("member",I("c"),states),Ex(Equal(state,I("c")),B("z",zType))),B("c",c));
        var conclusion=Ex(And(cutSpec,Call("Injective",Call("jointCutMap",cuts)),membership,
            Call("le",Call("NatCard",zType),Mul(Call("card",states),Add(k,D(1))))),
            B("cuts",Fn(zType,Call("Frame",c,I("Label")))),B("states",Call("Finset",c)));
        var premises=And(Call("Finite",zType),Call("Processing",action,initial,Call("OperationRecord",o,b,contract)),
            Call("OperationSafety",action,initial,o,b,contract),Call("OperationLiveness",action,initial,o,b,contract),
            actual,past,future,stems,difference,Call("Injective",alpha));
        return Disp(All(Imp(premises,conclusion),B("Configuration",I("Type")),B("Z",I("Type")),
            B("action",Fn(c,Call("Op",c,I("Color"),I("Label")))),B("initialConfiguration",c),
            B("o",I("Ownership")),B("b",I("Real")),B("contract",I("Contract")),
            B("alpha",Fn(zType,Fn(nat,I("Label")))),B("beta",Fn(zType,Fn(nat,I("Label")))),
            B("highRecord",Fn(zType,Fn(nat,I("Color")))),B("lowRecord",Fn(zType,Fn(nat,I("Color")))),
            B("n",nat),B("w",Call("List",I("Label")))));
    }


    private static Formula Ex(Formula body,params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.Exists,[.. vars],body);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Fn(Formula a,Formula b) => Call("Function",a,b);
    private static Formula BudgetRange()
    {
        var scale=Mul(Pow(I("g"),D(2)),Pow(I("chi"),I("K")));
        var fixedState=Call("divide",Call("aSide",I("high")),Sub(D(1),Mul(I("rho"),Pow(I("chi"),I("K")))));
        return And(Call("le",D(2),I("K")),
            Call("lt",Sub(I("lam"),Mul(scale,Call("hSide",I("high")))),I("b")),
            Call("lt",I("b"),Sub(I("lam"),Mul(scale,fixedState))));
    }
    private static Formula Threshold => Call("divide",Call("divide",Sub(I("lam"),I("b")),Pow(I("g"),D(2))),Pow(I("chi"),I("K")));
    private static Formula WeakBook(Formula model,Formula n) => Call("WeakCodebook",I("K"),Threshold,model,n);
    private static Formula ResetCost => Add(D(2,0),Mul(D(6),Call("m",I("R"))));
    private static Formula BookLength => Add(I("N"),ResetCost);
    private static Formula EqualWeightCodebook()
    {
        var words=I("words");var xs=I("xs");var model=I("targetModel");var n=I("N");
        var weak=And(Call("GuardTrace",I("K"),Threshold,I("false"),I("high"),xs,Call("initial",I("high"),I("sourceModel"))),Equal(Call("listWeight",xs),n));
        var admissible=All(Imp(Call("member",xs,words),weak),B("xs",Returns));
        var joint=All(Imp(admissible,And(
            Call("ActualPairSupply",model,I("o"),Sub(I("b"),I("eps")),I("closed"),Call("resetConcatenation",I("R"),words)),
            All(Call("ActualPairSupply",model,I("o"),I("b"),I("contract"),Call("resetConcatenation",I("R"),words)),B("contract",I("Contract"))),
            Equal(Call("listWeight",Call("resetConcatenation",I("R"),words)),Mul(Call("length",words),BookLength)))),
            B("targetModel",I("Model")),B("words",Call("List",Returns)));
        var counts=All(Call("le",Pow(Call("NatCard",WeakBook(I("sourceModel"),n)),I("q")),
            Call("NatCard",Call("ExactActualPairFamily",model,I("o"),I("b"),I("contract"),Mul(I("q"),BookLength)))),
            B("targetModel",I("Model")),B("contract",I("Contract")),B("q",I("Nat")));
        var books=All(Imp(Call("lt",D(0),n),And(Call("Finite",WeakBook(I("sourceModel"),n)),
            Ex(And(Call("lt",D(0),I("eps")),Call("lt",D(0),BookLength),joint,counts),B("eps",I("Real"))))),
            B("sourceModel",I("Model")),B("N",I("Nat")));
        return Disp(All(Imp(BudgetRange(),Ex(And(Equal(Call("r",I("R")),D(1)),books),B("R",I("Return")))),
            B("o",I("Ownership")),B("b",I("Real")),B("K",I("Nat"))));
    }
    private static Formula OperationPremises()
    {
        var c=I("Configuration");var nat=I("Nat");var action=I("action");var init=I("initialConfiguration");
        var record=Call("OperationRecord",I("o"),I("b"),I("contract"));
        var r=I("recordInput");var source=I("address");var t=I("t");
        var initial=Call("frame",init,D(0),I("nil"));
        var safe=All(Imp(And(Call("apply",record,source,r),Call("Run",action,Call("full",r),initial,t),
            Call("lt",I("p"),Call("length",Call("output",t)))),Equal(Call("get",Call("output",t),I("p")),Call("apply",source,I("p")))),
            B("address",Fn(nat,I("Label"))),B("recordInput",Fn(nat,I("Color"))),B("t",Call("Frame",c,I("Label"))),B("p",nat));
        var live=All(Imp(And(Call("apply",record,source,r),Call("OperationFiniteSource",source)),
            Ex(And(Call("Run",action,Call("full",r),initial,t),Call("lt",I("p"),Call("length",Call("output",t)))),B("t",Call("Frame",c,I("Label"))))),
            B("address",Fn(nat,I("Label"))),B("recordInput",Fn(nat,I("Color"))),B("p",nat));
        var f=I("f");var outword=I("outword");var batch=I("batch");var q=I("q");
        var post=All(Imp(And(Call("apply",record,source,r),
            Call("Run",action,Call("full",r),initial,Call("frame",I("c"),q,outword)),
            Equal(Call("apply",action,I("c")),Call("acquire",f)),
            Equal(Call("apply",f,Call("apply",r,q)),Call("some",Call("pair",I("d"),batch)))),
            Ex(Call("Drain",action,Call("frame",I("d"),Add(q,D(1)),Call("append",outword,batch)),t),B("t",Call("Frame",c,I("Label"))))),
            B("address",Fn(nat,I("Label"))),B("recordInput",Fn(nat,I("Color"))),B("c",c),B("d",c),B("q",nat),
            B("outword",Call("List",I("Label"))),B("batch",Call("List",I("Label"))),
            B("f",Fn(I("Color"),Call("Option",Call("Product",c,Call("List",I("Label")))))));
        return And(BudgetRange(),safe,live,post,
            Call("InjOn",I("encoding"),Call("AllActualReachable",action,init,record)));
    }
    private static Formula CompletePeak => Call("PeakFunction",I("action"),I("initialConfiguration"),
        Call("OperationRecord",I("o"),I("b"),I("contract")),I("encoding"));
    private static Formula PeakRatioLiminf => Call("liminfAtTop",Call("CompletePeakRatio",CompletePeak));
    private static Formula StorageTelescope(Formula body) => Disp(All(Imp(OperationPremises(),body),
        B("Configuration",I("Type")),B("action",Fn(I("Configuration"),Call("Op",I("Configuration"),I("Color"),I("Label")))),
        B("initialConfiguration",I("Configuration")),B("o",I("Ownership")),B("b",I("Real")),B("contract",I("Contract")),
        B("K",I("Nat")),B("encoding",Fn(I("Configuration"),Call("List",I("Bool"))))));
    private static Formula CodebookStorage()
    {
        var a=Call("NatCard",WeakBook(I("sourceModel"),I("N")));var delta=Call("observationOffset",I("model"));
        var horizon=I("H");var bound=I("B");var loga=Call("logb",D(2),Call("toReal",a));
        var floor=Call("toReal",Call("natDivide",Sub(horizon,delta),BookLength));
        var finite=All(Imp(And(Call("le",delta,horizon),Call("le",Call("apply",CompletePeak,horizon),Call("toWithTop",bound))),
            Call("le",Sub(Mul(floor,loga),D(1)),Call("toReal",bound))),B("H",I("Nat")),B("B",I("Nat")));
        var coefficient=Call("le",Call("ofReal",Call("divide",loga,Call("toReal",BookLength))),PeakRatioLiminf);
        var books=All(Imp(Call("lt",D(0),I("N")),Imp(Call("le",D(1),a),
            All(And(finite,coefficient),B("model",I("Model"))))),B("sourceModel",I("Model")),B("N",I("Nat")));
        return StorageTelescope(Ex(And(Equal(Call("r",I("R")),D(1)),books),B("R",I("Return"))));
    }
    private static Formula CompleteStorageRate() => StorageTelescope(All(
        Call("le",Call("ofReal",Call("WeakListRate",I("K"),Threshold,I("sourceModel"))),PeakRatioLiminf),B("sourceModel",I("Model"))));


    private static Formula TailOrbit()
    {
        var t=I("T");var x=I("x");var a=I("a");var y=I("y");
        var f=Call("CenteredAffine",y,a);
        var orbit=All(Call("member",Call("iterateApply",f,I("n"),x),t),B("n",I("Nat")));
        var positive=And(Call("member",x,t),Call("member",y,Call("closure",t)));
        var negative=And(Call("member",x,t),Call("member",Call("apply",f,x),t));
        var criterion=All(new Formula.Logic(orbit,FormulaLogicOperator.Iff,
            Call("ifThenElse",Call("lt",D(0),a),positive,negative)),B("x",I("Real")));
        var nonempty=new Formula.Logic(Ex(orbit,B("x",I("Real"))),FormulaLogicOperator.Iff,
            Call("ifThenElse",Call("lt",D(0),a),And(Call("Nonempty",t),Call("member",y,Call("closure",t))),Call("member",y,t)));
        return Disp(All(Imp(And(Call("OrdConnected",t),Call("lt",Call("negate",D(1)),a),Call("lt",a,D(1)),Call("notEqual",a,D(0))),
            And(criterion,nonempty)),B("T",Call("Set",I("Real"))),B("a",I("Real")),B("y",I("Real"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-competing-tail-orbit-criterion"),DeclarationHandle.Create(Prefix+"competing_tail_orbit_criterion"),
                H("Endpoint-sensitive scalar competing-tail orbits"),StatementSource.FromAuthor(TailOrbit()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CenteredAffine(y,a)(x)=y+a(x-y), and iterateApply(f,n,x)=f^[n](x). T is any order-connected real set, including empty and singleton intervals. For 0<a<1 the full orbit condition is x in T and y in closure(T); membership of y itself is unnecessary. For -1<a<0 it is x in T and f(x) in T; these two actual members also force y in T, and this is equivalent to a nonempty feasible orbit set. Positive iterates converge to y and lie strictly between the initial point and y; negative iterates remain in the closed segment between x and f(x). Actual open and closed endpoint membership is retained.")),
                    Paragraph(Text("This is the scalar interval part of the original39.5 criterion. Constructing the original finite budget intersection, its owned endpoint flags and legal Omega tails remains source-side work; no tail is inferred from a scalar member here. An optional original-piece restriction requires a member of the feasible orbit set in that piece and is imposed only when present in the family. Original39.4 finite D-tail selection and the full arbitrary-k original39.7 construction remain open."))),DescribeRole.Theorem),

            Describe.Lean(DescribeId.Create("fib-original-equal-weight-codebook"),DeclarationHandle.Create(Prefix+"original_equal_weight_codebook"),
                H("Full finite weak codebooks with one reset at every seam"),StatementSource.FromAuthor(EqualWeightCodebook()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("WeakCodebook(K,d,sourceModel,N) is the entire subtype of return lists xs with GuardTrace K d false high xs (initial high sourceModel) and listWeight xs=N. The single reset R is chosen before sourceModel and N. Its r is one and C_R=20+6R.m. resetConcatenation(R,[]) is []; resetConcatenation(R,xs::words) is (R::xs) appended to resetConcatenation(R,words). Each chosen word receives this same reset. For every N>0 the full subtype is finite. The positive eps may depend on N and sourceModel, but works for every finite joint choice, every target model and every number of seams. It supplies the actual paired sources at closed budget b-eps and hence all three contracts at b. Their fixed literal tails and zero-error futures are those of ActualPairSupply. The total weight is q(N+C_R).")),
                    Paragraph(Text("The reset state strictly exceeds either initial state. The affine difference over every word prefix is bounded below by (B-D)g^N; choosing eps below a fixed multiple of that gap makes each high guard strict at every seam. The exact positive weights recover equal-weight words from their cumulative cuts, even when their return-list lengths differ. Thus all q-tuples inject into actual lists and give at least NatCard(WeakCodebook)^q members. Empty and unsupported codebooks and q=0 are included. No common margin over all weights is asserted."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-original-codebook-storage-liminf"),DeclarationHandle.Create(Prefix+"original_codebook_storage_liminf"),
                H("All observation horizons force the exact codebook coefficient"),StatementSource.FromAuthor(CodebookStorage()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("AllActualReachable consists of configurations c for which ReachThrough(H,c) holds for some H. The supplied encoding is injective on this complete set. PeakFunction(H) is the WithTop Nat supremum of encoding lengths over all records and all primitive vertices through H. CompletePeakRatio(H) is ENat.toENNReal(PeakFunction(H))/(H:ENNReal), and liminfAtTop is its lower limit over natural observation horizons. Safety, positionwise D liveness and finite drains after actual acquisitions are expanded in the displayed premises; no independent startup premise is supplied. Actual empty-list high/low records have distinct first labels, so these contracts derive finite startup.")),
                    Paragraph(Text("For every fixed N>0 with a=NatCard(WeakCodebook)>=1, L=N+C_R is positive and Delta is the original 26 or anchored 52. The exhaustive actual-operation separation and full variable-length capacity yield a^q<=2^(B+1)-1 at Delta+qL. Monotonicity of the complete peak transfers this bound to q=floor((H-Delta)/L) for every H>=Delta. Thus q log2(a)-1<=B whenever the full peak is bounded by B. Floor interpolation has a fixed-codebook loss divided by H, which tends to zero. Infinite peaks are treated as top, without finite conversion. The resulting necessary lower-limit coefficient is exactly log2(a)/(N+C_R)."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-original-complete-storage-liminf"),DeclarationHandle.Create(Prefix+"original_complete_storage_liminf"),
                H("The original weak-list rate is a necessary full-storage lower limit"),StatementSource.FromAuthor(CompleteStorageRate()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("WeakListRate(K,d,sourceModel) is limsup atTop of logb 2 (max 1 (NatCard(WeakCodebook(K,d,sourceModel,n))))/n, with the casts and zero-denominator convention of Lean Real. Every fixed codebook coefficient is bounded by the same full-storage liminf. If that liminf is infinite the result holds directly. Otherwise its finite real value bounds all shifted coefficients. The factor n/(n+C_R) tends to one, and the limsup product inequality recovers the weak-list rate without assuming exact-weight count monotonicity. The preserved anonymous37 equality identifies this rate with the independent factor and original actual contract rates; no rate proof is replaced here.")),
                    Paragraph(Text("The statement concerns the explicit primitive operation presentation and the supplied original complete encoding. Every readable quantity belongs to Configuration; Frame acquisition and output fields are external bookkeeping. An implementation must represent every actual instruction and charged intermediate state at that granularity. Universal correspondence to every prose decoder and independent authored-formula fidelity are separate from this conditional operational mathematics. No single additive constant at the limiting rate and no attaining decoder are asserted."))),DescribeRole.Theorem),

            Describe.Lean(DescribeId.Create("fib-original-operation-decoder-storage"),
                DeclarationHandle.Create(Prefix+"original_operation_decoder_storage"), H("Actual primitive cuts and the complete encoding peak"),
                StatementSource.FromAuthor(OperationStorage()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("OperationOmega(a,x) is exactly the original legal supported affine path: path starts at G0, follows nextGuard on a, supports x at each position, and x(p)=branch(a(p),x(p+1)). OperationRecord(o,b,contract)(a,r) supplies that path and an original ErrorBound error with observe(o,x(p),err(p))=r(p) at every position. OperationFiniteSource is eventual L0. OperationSafety and OperationLiveness quantify every such original record and every finite primitive trace, with positionwise liveness on eventual L0 sources. Processing includes the real startup drain and actual post-acquisition drains, with no global termination on unreachable states.")),
                    Paragraph(Text("ExactActualPairFamily is the subtype of all return lists satisfying ActualPairSupply(model,o,b,contract) and listWeight=N, without sampling or weight monotonicity. The original anonymous45 finite-family construction is reused. Every cut is constructed from actual D liveness. Its high and low paired records share history(model,xs); the same retained primitive past trace embeds on the low record. Safety and the actual L5/L0 first difference force the output word to be empty. Equal original cut states replay the same literal high future; safety and positionwise D liveness recover equal addresses and the original source injection recovers the return lists. Cut uniqueness follows primitive determinism at input exhaustion.")),
                    Paragraph(Text("stateCutMap(cuts)(x) is state(cuts(x)). states is its finite image, whose cardinal is exactly NatCard of the exhaustive family. The history length is observationOffset(model)+N, namely 26+N for original and 52+N for anchored. AllActualReachable means configurations in ReachThrough(H) for some H. The supplied original complete encoding is injective on that set. PeakFunction is H mapped to the full WithTop Nat encoding-length supremum over every actual record and primitive intermediate state. A finite peak bound B yields at most 2^(B+1)-1 variable-length codes. Fixed complete width B at the selected states yields at most 2^B codes. Infinite peaks and empty or unsupported exact-weight families remain included. Every trace vertex in the horizon is bounded by this full peak.")),
                    Paragraph(Text("This result is for the explicit primitive operation presentation. It proves neither universal representation of every prose decoder nor the source initialization and endpoint correspondence. The equal-weight codebook and complete-storage lower-limit results provide the additional necessary coefficient argument. Independent authored-formula equivalence, original fidelity and canonical admission remain separate obligations."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-original-operation-common-stem"),
                DeclarationHandle.Create(Prefix+"original_operation_common_stem"), H("One fixed actual stem gives the original prefix factor"),
                StatementSource.FromAuthor(OperationStem()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite supplied family has actual alpha records in eventual L0 and actual beta records in Omega, using precisely OperationRecord and all original error contracts and endpoint flags. Each high and low record shares the same n acquired colors for its family member. The high unread future is the same across members; the low future may differ. The single word w is fixed independently of the family member. Both actual addresses agree with w before its length and differ at that position; sourceInjection concerns alpha addresses only and is a source-side hypothesis.")),
                    Paragraph(Text("Actual high-side liveness constructs each cut, and primitive past transfer supplies the beta run without assuming progress on all Omega records. Safety at the first disagreement bounds old output length by length(w); safety before it gives output=take(w,length(output)) and prefix membership. Equal cut state and old word then permit unread-suffix replay, forcing equal alpha addresses and equal family members. jointCutMap is the external pair of cut state and cumulative old word. Prefix length injects the possible words into Fin(length(w)+1). Counting the finite state image times that many prefix tags gives NatCard(Z) at most card(states)*(length(w)+1). The old word is never readable storage. No prefix or joint decoder injection is assumed.")),
                    Paragraph(Text("This theorem requires actual source-side witnesses and preserves their fixed-stem and common-future scope. The original39.7 construction supplying those witnesses is not newly formalized here. It is not a standalone product-cardinality result and does not change the retained k0 source family."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-complete-boundary-geometry"),
                DeclarationHandle.Create(Prefix + "actual_complete_boundary_geometry"), H("Actual complete boundaries and internal inputs"),
                StatementSource.FromAuthor(BoundaryGeometry()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prefix of the common execution list, both actual initial states retain A_j < D_j < h_j and the high displacement is smaller than the low displacement. Internal inputs obtained by any number of C contractions and six-letter affine iterates remain positive and below h_j, keep the same side ordering, and their signed coordinates belong to [0,T2]. Each complete boundary is identified with the coordinate at stem length plus the weight of the unexecuted suffix in the same fixed source. The lower bound A_j is asserted only at complete boundaries, not at arbitrary internal cuts."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-strict-record-supply"),
                DeclarationHandle.Create(Prefix + "actual_strict_record_supply"),
                H("Strict and per-record-margin supply on the original paired sources"),
                StatementSource.FromAuthor(StrictRecordSupply()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For K at least two and the original transition budget q_K < b < Psi_K, strict supply and per-record positive-margin supply of the independently defined actual source pair are each equivalent to the exact cap and strict high guard. The proof derives acquisition for arbitrary repetitions of the original six- and twenty-letter blocks, assembles all errors on the fixed same-list literal sources, and reads their original futures with zero error. It pays the stem and every repeated return, and the anchored template pays its own anchor using chi times X_H. Returns above the cap are rejected at the actual control cost; low returns are strictly supplied. Finite history errors give a positive margin for each record, without a common margin for an infinite family. All five endpoint flags remain arbitrary."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-closed-record-supply"),
                DeclarationHandle.Create(Prefix + "actual_closed_record_supply"),
                H("Closed supply and owned high-guard equality"),
                StatementSource.FromAuthor(ClosedRecordSupply()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either fixed original or anchored source pair, closed acquisition is equivalent to the cap and high guard. Owning the first cut point permits equality; otherwise the high guard is strict. The proof assembles all departure errors on those same literal sources, through every six- and twenty-slot repetition, stem and paid anchor, and extends them by zero on the unchanged original futures. High equality uses the owned nearest point from the actual clipped readout law. The paired low costs are strictly smaller. All five flags remain parameters, and returns beyond the cap fail at the actual control slot."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-reset-first-return"),
                DeclarationHandle.Create(Prefix + "actual_reset_first_return"),
                H("One paid actual reset and first-return output dominance"),
                StatementSource.FromAuthor(ResetFirstReturn()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A single positive finite reset length M gives B_M greater than X_H, Y_H and d. Its actual input above A gives output strictly above B_M; an input at least A gives the stated weak bound. Prepending this same reset to any weakly guarded complete list from either actual start supplies the complete paired record strictly from either target start, including the stems, anchor and original zero-error futures. The weight increases by exactly 20+6M. The exact first-run insertion identity gives strict output dominance after one added u for every original m,r,z in the stated domain. This extra u follows the first visible c-run even when it is low; no undiminished reset margin is assigned to a later return."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-complete-execution-word-parser"),
                DeclarationHandle.Create(Prefix + "complete_execution_word_parser"),
                H("Maximal complete runs and original history injection"),
                StatementSource.FromAuthor(CompleteParser()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The initial maximal c-run has exactly r letters and the following maximal u-run has exactly m letters for every positive return. Recursing after those runs uniquely recovers the complete execution list. Its weight is exactly the original list weight with c charged 20 and u charged 6. The actual color blocks have different second colors, so their concatenation is injective. Reversing only the execution-letter word produces the external block order without reversing any color-block letters. Removing the fixed common stem and paid anchor proves history injection for each actual model."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-bilateral-past-state"),
                DeclarationHandle.Create(Prefix + "bilateral_past_state"),
                H("Independent finite-past state and bounded bilateral uniqueness"),
                StatementSource.FromAuthor(BilateralPast()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The auxiliary letter maps are c: z maps to chi*z and u: z maps to A_H+rho*z, with the original high-side constants. The finite past at i composes the N letters immediately before i in chronological order. Its exact seed difference is g raised to their original 20/6 weight times the seed difference, bounded by rho^N. The zero-seed sequence is increasing and bounded in [0,h_H]; its supremum is the independently defined pastState. Every seed in that interval has the same limit. This state satisfies the letter transition law and is the unique bilateral solution confined to [0,h_H]. Two sequences agreeing on the last N past letters have states differing by at most h_H*rho^N. The all-u state equals h_H. In the formula, Sequence denotes the function of N and const(u) denotes the constant bilateral u sequence.")),
                    Paragraph(Text("Matching-past stability gives continuity in the product of the discrete letter spaces. AuxiliaryLanguage forbids K+1 consecutive c letters and checks chi^(K-1)*d before a current c whose preceding K-1 letters are c. For K at least one and every real d, the all-u sequence belongs to this closed compact language. States commute with every integer shift, where shift(omega,j)(n)=omega(n+j), and membership is invariant under those shifts. AuxiliaryFactor is defined by an actual occurrence in a sequence satisfying those independent conditions; neither object is a completion image or an actual literal source."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-auxiliary-lower-padding"),
                DeclarationHandle.Create(Prefix + "auxiliary_lower_padding"),
                H("Literal auxiliary padding of weak complete actual lists"),
                StatementSource.FromAuthor(LowerPadding()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For K at least one, any real guard d and either actual initial model, a weakly guarded complete return list has its exact execution word at the origin of uPadding. This sequence equals that finite word at nonnegative positions inside it, and equals u at every other integer position. Its infinite-past state at zero is h_H. At every complete return boundary its state strictly exceeds the state of the original actual recurrence. Every c position is located in an original return; the intervening positive u runs prevent a K-letter guard from crossing a return boundary. The cap excludes K+1 consecutive c letters, and the weak actual guard transfers to the independent before-Kth-c auxiliary guard. The exact finite word occurs at zero and is an AuxiliaryFactor, with weight equal to listWeight. Combined directly with the existing complete execution parser, this supplies an injection of exact-weight weak complete lists into distinct occurrence factors. Empty lists are included. The auxiliary u tails do not replace either original eventually-empty literal source or its zero-error future. castInt is the natural-to-integer inclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-finite-run-decomposition"),
                DeclarationHandle.Create(Prefix + "finite_run_decomposition"),
                H("Unique decomposition of arbitrary terminal-u words"),
                StatementSource.FromAuthor(FiniteRunDecomposition()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite c/u word that is empty or ends in u has exactly one decomposition into a leading u run and a positive complete return list. The leading run may be empty; the return list may be empty for an all-u word. The existence proof constructs the runs by induction on the literal letters; uniqueness directly reuses the complete execution parser. The displayed two-variable existential with equality of every alternative pair is the unique-existence statement on Nat times List Return. getLastOption denotes getLast?."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-occurrence-run-guards"),
                DeclarationHandle.Create(Prefix + "occurrence_run_guards"),
                H("Independent occurrence guards on canonical complete runs"),
                StatementSource.FromAuthor(OccurrenceRunGuards()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The bilateral sequence independently belongs to AuxiliaryLanguage. Its letters agree with the prescribed complete execution word at every position except that the final u may have been appended as a terminal fill. All c letters must still agree. Each run inherits the cap from the original forbidden K+1 c letters. At a run of length K, the original state before its last c is chi^(K-1) times its run-start state, so the independent before-Kth-c guard yields the weak return guard. When another return follows, every intervening u is an original occurrence letter and the exact transition law aligns its next start. No state alignment is claimed across an appended terminal u."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-auxiliary-factor-upper-completion"),
                DeclarationHandle.Create(Prefix + "auxiliary_factor_upper_completion"),
                H("Strict actual completion of every c-containing occurrence factor"),
                StatementSource.FromAuthor(UpperCompletion()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One fixed reset R has r equal to one. For either actual model and every independently occurring factor containing c, append one terminal u precisely when its last letter is c. The filled word has a unique leading u run of length a followed by first and rest positive returns. Merge that leading run into the reset by replacing its m with R.m+a; add one u after the first visible c-run by replacing first.m with first.m+1. The resulting complete list strictly supplies the original actual paired sources, with all endpoint flags, stems, paid anchor and unchanged zero-error futures. The proof uses the occurrence guards, the reset output bound and the original first-return strict output dominance. Subsequent common transitions strictly preserve dominance. Truncated first and last runs, a low first return and first equal to last are all included; no common family margin follows.")),
                    Paragraph(Text("Serialization is the displayed normal form c u^(R.m+a) c^first.r u^(first.m+1) executionWord(rest). The exact weight overhead is 20+6R.m+6 for an original u ending and 20+6R.m+12 for an original c ending. Return(m,r) in the formula specifies the two positive exponents; the Lean constructors include their positivity proofs. This theorem proves actual membership and the unique run decomposition, not a finite-cardinality count or a rate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-source-address-injection"),
                DeclarationHandle.Create(Prefix + "actual_source_address_injection"),
                H("Actual equal-weight source addresses determine their lists"),
                StatementSource.FromAuthor(SourceAddressInjection()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either actual side and either model, two return lists of the same variable weight have equal full eventually-empty source addresses only if the lists are equal. Equality of addresses determines the finite observed prefixes because their original lengths coincide. Removing the same stem and paid anchor leaves equal external label words. On the high side U and C have different second labels; on the low side V and C have different first labels. The label-block encoding is therefore uniquely recoverable. Reversing the execution-letter order preserves the letters inside each original block, and the existing complete execution parser recovers the return list. The two literal tails remain unchanged. This is a statement about literal addresses; it does not assert injectivity of the scalar coordinate or establish an asymptotic rate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-decoder-configuration-extraction"),
                DeclarationHandle.Create(Prefix + "actual_decoder_configuration_extraction"),
                H("Complete configurations separate actual paired records"),
                StatementSource.FromAuthor(DecoderConfigurationExtraction()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An acquisition stage takes a complete readable configuration and the next color, performs its finite computation, and returns the next configuration and a finite ordered output batch. All control, counters, timing, positions and readable output-side information belong to Configuration. The transition does not read the cumulative emitted word. appendOutputStep(advance)((q,v),c) is (q',v concatenated with batch), where advance(q,c)=(q',batch). foldl starts at the fixed initial configuration and initial output. runHistory and configurationHistory apply this recurrence to history(model,xs), taking respectively the joint pair and its first component. Safety is required for every supported legal affine source and actual error-bounded record; liveness requires each position, including L0 positions, at a finite acquisition stage of every eventually-L0 source.")),
                    Paragraph(Text("pairedRecord(model,o,xs,j)(p) equals history(model,xs)[p] while p is less than its length M, and equals observe(o,coordinate(tailPrefix(j),p-M),0) thereafter. Its actual error witness, guard path, supported coordinate path and eventual empty tail are constructed from the original paired supply and source reconstruction. Thus the M departures are acquired once, the terminal M is unobserved at the cut, and the original literal future starts there. The original and anchored offsets are 26 and 52; the weight N may be zero or unsupported, and the family may be empty. Every endpoint flag and each original contract remains a parameter.")),
                    Paragraph(Text("The high stem begins with L5 and the low stem with L0, so their actual first differing position is k=0. Safety on both continuations forces the cumulative output at the common departure cut to be empty. In general the prefix factor would be k+1; here it is 0+1. Equal cut configurations therefore give equal joint pairs. Folding either pair along the same high-side literal future gives identical subsequent output. Positionwise finite liveness and safety then equate the two high source addresses, and equal-weight actual address separation recovers the lists. The joint and configuration maps are injective and the number of family members is at most the number of reached complete configurations times one. The emitted word supplies no readable memory. This finite lower bound applies to each compliant transition semantics; it asserts no upper bound on inefficient decoders and no storage-capacity estimate without a configuration encoding."))),
                DescribeRole.Theorem),
            Paragraph(Text("The classwise deletion and finite exact-weight cardinality applications are separate from the retained run and actual-membership declarations. The finite configuration lower bound uses full actual supply, safety and positionwise liveness. A lower or upper occurrence map alone does not supply a common positive margin for an infinite family.")))));
}
