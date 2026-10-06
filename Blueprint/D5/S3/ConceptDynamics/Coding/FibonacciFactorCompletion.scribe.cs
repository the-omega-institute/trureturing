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

    private static Formula TailPath(Formula s, Formula a, Formula x, Formula q) => And(
        Equal(Call("apply",q,D(0)),s),
        All(Equal(Call("nextGuard",Call("apply",q,I("p")),Call("apply",a,I("p"))),
            Call("some",Call("apply",q,Add(I("p"),D(1))))),B("p",I("Nat"))),
        All(Call("InSupport",Call("apply",q,I("p")),Call("apply",x,I("p"))),B("p",I("Nat"))),
        All(Equal(Call("apply",x,I("p")),Call("branch",Call("apply",a,I("p")),
            Call("apply",x,Add(I("p"),D(1))))),B("p",I("Nat"))));
    private static Formula TailPrefix(Formula w, Formula a) => All(Imp(Call("lt",I("p"),Call("length",w)),
        Equal(Call("apply",a,I("p")),Call("getElem",w,I("p")))),B("p",I("Nat")));
    private static Formula TailFuture(Formula w, Formula a, Formula tail) => All(
        Equal(Call("apply",a,Add(Call("length",w),I("p"))),Call("apply",tail,I("p"))),B("p",I("Nat")));
    private static Formula TailHullSupport => All(Imp(And(Call("le",I("lo"),I("z")),Call("le",I("z"),I("hi"))),
        Call("InSupport",I("s"),I("z"))),B("z",I("Real")));
    private static Formula TailLawful() => Disp(All(Imp(Call("InSupport",I("s"),I("z")),
        Ex(And(TailPath(I("s"),I("a"),I("x"),I("path")),Equal(Call("apply",I("x"),D(0)),I("z"))),
            B("a",Fn(I("Nat"),I("Label"))),B("x",Fn(I("Nat"),I("Real"))),B("path",Fn(I("Nat"),I("Guard"))))),
        B("s",I("Guard")),B("z",I("Real"))));
    private static Formula TailApproximation() => Disp(All(Imp(And(Call("InSupport",I("s"),I("z")),Call("lt",D(0),I("epsilon"))),
        Ex(And(Call("LegalWord",I("s"),I("e"),I("w")),
            Call("lt",Call("abs",Sub(I("z"),Call("coordinate",I("w"),D(0)))),I("epsilon"))),
            B("e",I("Guard")),B("w",Call("List",I("Label"))))),
        B("s",I("Guard")),B("z",I("Real")),B("epsilon",I("Real"))));
    private static Formula TailInterior() => Disp(All(Imp(And(Call("lt",I("lo"),I("hi")),TailHullSupport),
        Ex(And(Call("LegalWord",I("s"),I("e"),I("w")),
            Call("lt",I("lo"),Call("coordinate",I("w"),D(0))),Call("lt",Call("coordinate",I("w"),D(0)),I("hi")),
            Call("OperationFiniteSource",Call("address",I("w"))),
            Ex(TailPath(I("s"),Call("address",I("w")),Call("coordinateSequence",I("w")),I("path")),
                B("path",Fn(I("Nat"),I("Guard"))))),B("e",I("Guard")),B("w",Call("List",I("Label"))))),
        B("s",I("Guard")),B("lo",I("Real")),B("hi",I("Real"))));
    private static Formula TailPrepend() => Disp(All(Imp(And(Call("LegalWord",I("s"),I("e"),I("w")),
        TailPath(I("e"),I("a"),I("x"),I("path"))),
        Ex(And(TailPath(I("s"),I("beta"),I("X"),I("q")),
            Equal(Call("apply",I("X"),D(0)),Call("compose",I("w"),Call("apply",I("x"),D(0)))),
            TailPrefix(I("w"),I("beta")),TailFuture(I("w"),I("beta"),I("a")),TailFuture(I("w"),I("X"),I("x"))),
            B("beta",Fn(I("Nat"),I("Label"))),B("X",Fn(I("Nat"),I("Real"))),B("q",Fn(I("Nat"),I("Guard"))))),
        B("s",I("Guard")),B("e",I("Guard")),B("w",Call("List",I("Label"))),
        B("a",Fn(I("Nat"),I("Label"))),B("x",Fn(I("Nat"),I("Real"))),B("path",Fn(I("Nat"),I("Guard")))));
    private static Formula TailColor(string kind)
    {
        var o=I("o");var c=I("c");var z=I("z");var theta=I("theta");
        var interval=Call("FlagInterval",Sub(Call("cut",Call("val",c)),theta),
            Add(Call("cut",Add(Call("val",c),D(1))),theta),Call("lowerOwned",o,c),Call("upperOwned",o,c),z);
        var owned=Call("OwnedColor",o,theta,c,z);var support=Call("InSupport",I("G0"),z);
        Formula formula;
        if(kind=="cell") formula=new Formula.Logic(Call("Cell",o,c,z),FormulaLogicOperator.Iff,
            Call("FlagInterval",Call("cut",Call("val",c)),Call("cut",Add(Call("val",c),D(1))),
                Call("lowerOwned",o,c),Call("upperOwned",o,c),z));
        else if(kind=="interval") formula=Imp(Call("le",D(0),theta),new Formula.Logic(owned,FormulaLogicOperator.Iff,And(support,interval)));
        else if(kind=="error") formula=Imp(support,new Formula.Logic(owned,FormulaLogicOperator.Iff,
            Ex(And(Call("le",Call("abs",I("error")),theta),Equal(Call("observe",o,z,I("error")),c)),B("error",I("Real")))));
        else formula=Imp(Call("le",D(0),theta),Call("OrdConnected",Call("setOfOwnedColor",o,theta,c)));
        if(kind=="cell") return Disp(All(formula,B("o",I("Ownership")),B("c",I("Color")),B("z",I("Real"))));
        if(kind=="connected") return Disp(All(formula,B("o",I("Ownership")),B("theta",I("Real")),B("c",I("Color"))));
        return Disp(All(formula,B("o",I("Ownership")),B("theta",I("Real")),B("c",I("Color")),B("z",I("Real"))));
    }
    private static Formula TailT => Call("CompetingT",I("o"),I("theta"),I("s"),I("Q"),I("V"),I("h"),I("W"));
    private static Formula TailCompeting(string kind)
    {
        Formula result=kind=="interval" ? Imp(Call("le",D(0),I("theta")),Call("OrdConnected",TailT)) :
            Imp(And(Call("LegalWord",I("G0"),I("s"),I("Q")),Call("LegalWord",I("s"),I("s"),I("V"))),
                new Formula.Logic(Call("member",I("z"),TailT),FormulaLogicOperator.Iff,
                    And(Call("InSupport",I("s"),I("z")),Call("BlockSupply",I("o"),I("theta"),I("false"),I("Q"),I("h"),I("z")),
                        All(Call("BlockSupply",I("o"),I("theta"),I("false"),I("V"),Call("apply",I("W"),I("i")),I("z")),B("i",I("Bool"))))));
        return Disp(All(result,B("o",I("Ownership")),B("theta",I("Real")),B("s",I("Guard")),
            B("Q",Call("List",I("Label"))),B("V",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
            B("W",Fn(I("Bool"),Call("List",I("Color")))),B("z",I("Real"))));
    }
    private static Formula TailCertificate() => Disp(All(Imp(And(Call("le",D(0),I("theta")),
        Call("EndpointCertificate",I("theta"),I("lo"),I("hi"),I("w"),I("cs")),
        Call("lt",I("lo"),I("x")),Call("lt",I("x"),I("hi"))),
        Call("BlockSupply",I("o"),I("theta"),I("false"),I("w"),I("cs"),I("x"))),
        B("o",I("Ownership")),B("theta",I("Real")),B("lo",I("Real")),B("hi",I("Real")),
        B("w",Call("List",I("Label"))),B("cs",Call("List",I("Color"))),B("x",I("Real"))));
    private static Formula TailHigh()
    {
        var choices=Call("choiceBlocks",I("R"),I("zs"));var colors=Call("choiceBlocks",I("W"),I("zs"));
        var prefix=Call("append",I("P"),choices);var cs=Call("append",I("h"),colors);var alpha=Call("address",Call("append",prefix,I("w")));
        var record=Call("recordWithTail",I("o"),cs,I("w"));
        var data=And(Call("le",D(0),I("theta")),Call("LegalWord",I("G0"),I("s"),I("P")),Equal(Call("length",I("P")),Call("length",I("h"))),
            All(And(Call("LegalWord",I("s"),I("s"),Call("apply",I("R"),I("i"))),
                Equal(Call("length",Call("apply",I("R"),I("i"))),Call("length",Call("apply",I("W"),I("i"))))),B("i",I("Bool"))),
            Call("lt",I("lo"),I("hi")),TailHullSupport,
            All(Imp(And(Call("le",I("lo"),I("z")),Call("le",I("z"),I("hi"))),
                And(Call("le",I("lo"),Call("compose",Call("apply",I("R"),I("i")),I("z"))),
                    Call("le",Call("compose",Call("apply",I("R"),I("i")),I("z")),I("hi")))),B("i",I("Bool")),B("z",I("Real"))),
            Call("EndpointCertificate",I("theta"),I("lo"),I("hi"),I("P"),I("h")),
            All(Call("EndpointCertificate",I("theta"),I("lo"),I("hi"),Call("apply",I("R"),I("i")),Call("apply",I("W"),I("i"))),B("i",I("Bool"))));
        var result=Ex(And(Call("LegalWord",I("s"),I("e"),I("w")),Call("lt",I("lo"),Call("coordinate",I("w"),D(0))),
            Call("lt",Call("coordinate",I("w"),D(0)),I("hi")),
            All(And(Call("OperationRecord",I("o"),I("theta"),I("closed"),alpha,record),Call("OperationFiniteSource",alpha),
                All(Equal(Call("apply",record,Add(Call("length",cs),I("p"))),Call("observe",I("o"),Call("coordinate",I("w"),I("p")),D(0))),B("p",I("Nat")))),
                B("zs",Call("List",I("Bool"))))),B("e",I("Guard")),B("w",Call("List",I("Label"))));
        return Disp(All(Imp(data,result),B("o",I("Ownership")),B("theta",I("Real")),B("s",I("Guard")),B("P",Call("List",I("Label"))),
            B("h",Call("List",I("Color"))),B("R",Fn(I("Bool"),Call("List",I("Label")))),B("W",Fn(I("Bool"),Call("List",I("Color")))),
            B("lo",I("Real")),B("hi",I("Real"))));
    }
    private static Formula TailLow()
    {
        var fv=Call("composeMap",I("V"));var a=I("a");var y=I("y");
        var feasible=Call("ifThenElse",Call("lt",D(0),a),And(Call("Nonempty",TailT),Call("member",y,Call("closure",TailT))),Call("member",y,TailT));
        var data=And(Call("le",D(0),I("theta")),Call("LegalWord",I("G0"),I("s"),I("Q")),Call("LegalWord",I("s"),I("s"),I("V")),
            Equal(Call("length",I("Q")),Call("length",I("h"))),
            All(Equal(Call("length",I("V")),Call("length",Call("apply",I("W"),I("i")))),B("i",I("Bool"))),
            Call("lt",Call("negate",D(1)),a),Call("lt",a,D(1)),Call("notEqual",a,D(0)),
            Equal(a,Pow(Call("negate",I("g")),Call("length",I("V")))),Equal(Call("compose",I("V"),y),y),feasible);
        var prefix=Call("append",I("Q"),Call("choiceBlocks",Call("constantWordFamily",I("V")),I("zs")));
        var cs=Call("append",I("h"),Call("choiceBlocks",I("W"),I("zs")));
        var result=Ex(And(TailPath(I("s"),I("tail"),I("x"),I("path")),
            All(Call("member",Call("iterateApply",fv,I("n"),Call("apply",I("x"),D(0))),TailT),B("n",I("Nat"))),
            All(Ex(And(Call("OperationOmega",I("beta"),I("X")),TailPrefix(prefix,I("beta")),
                TailFuture(prefix,I("beta"),I("tail")),TailFuture(prefix,I("X"),I("x")),
                Call("OperationRecord",I("o"),I("theta"),I("closed"),I("beta"),Call("recordWithOmegaTail",I("o"),cs,I("x")))),
                B("beta",Fn(I("Nat"),I("Label"))),B("X",Fn(I("Nat"),I("Real")))),B("zs",Call("List",I("Bool"))))),
            B("tail",Fn(I("Nat"),I("Label"))),B("x",Fn(I("Nat"),I("Real"))),B("path",Fn(I("Nat"),I("Guard"))));
        return Disp(All(Imp(data,result),B("o",I("Ownership")),B("theta",I("Real")),B("s",I("Guard")),
            B("Q",Call("List",I("Label"))),B("V",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
            B("W",Fn(I("Bool"),Call("List",I("Color")))),B("a",I("Real")),B("y",I("Real"))));
    }
    private static Formula TailSynchronous()
    {
        var action=I("action");var initial=I("initialConfiguration");var o=I("o");var theta=I("theta");var n=I("n");var z=I("z");
        var choices=Fn(Call("Fin",n),I("Bool"));var horizon=Add(Call("length",I("P")),Mul(n,I("L")));
        var high=Call("SynchronousHighSource",I("P"),I("U"),z,I("w"));
        var highRecord=Call("recordWithTail",o,Call("synchronousPrefix",I("h"),I("W"),z),I("w"));
        var lowRecord=Call("recordWithOmegaTail",o,Call("synchronousPrefix",I("h"),I("W"),z),I("x"));
        var beta=Call("apply",I("beta"),z);var cut=Call("apply",I("cuts"),z);var stem=Call("take",I("P"),I("k"));
        var data=And(Call("SynchronousSourceData",o,theta,I("s1"),I("s2"),I("P"),I("Q"),I("h"),I("U"),I("V"),I("W"),
            I("L"),I("lo"),I("hi"),I("a"),I("y"),I("k")),
            Call("ClosedOperationSafety",action,initial,o,theta),Call("ClosedOperationLiveness",action,initial,o,theta),
            Call("ExecutedPostprocessing",action,initial,o,theta));
        var family=And(
            All(And(Call("OperationRecord",o,theta,I("closed"),high,highRecord),Call("OperationFiniteSource",high)),B("z",choices)),
            All(Call("OperationRecord",o,theta,I("closed"),beta,lowRecord),B("z",choices)),
            All(TailPrefix(Call("synchronousPrefix",I("Q"),Call("constantWordFamily",I("V")),z),beta),B("z",choices)),
            All(Equal(Call("apply",beta,Add(horizon,I("p"))),Call("apply",I("eta"),I("p"))),B("z",choices),B("p",I("Nat"))),
            All(Equal(Call("apply",highRecord,Add(horizon,I("p"))),Call("observe",o,Call("coordinate",I("w"),I("p")),D(0))),B("z",choices),B("p",I("Nat"))),
            Call("Injective",Call("SynchronousHighFamily",I("P"),I("U"),n,I("w"))),
            All(And(Call("Cut",action,initial,Call("front",highRecord,horizon),cut),Call("le",Call("length",Call("output",cut)),I("k")),
                Equal(Call("output",cut),Call("take",stem,Call("length",Call("output",cut)))),Call("IsPrefix",Call("output",cut),stem)),B("z",choices)),
            Call("Injective",Call("cutStateOutputMap",I("cuts"))),
            All(new Formula.Logic(Call("member",I("c"),I("states")),FormulaLogicOperator.Iff,
                Ex(Equal(Call("state",cut),I("c")),B("z",choices))),B("c",I("Configuration"))),
            Call("le",Pow(D(2),n),Mul(Call("card",I("states")),Add(I("k"),D(1)))));
        var result=Ex(And(Call("LegalWord",I("s1"),I("e"),I("w")),Call("lt",I("lo"),Call("coordinate",I("w"),D(0))),
            Call("lt",Call("coordinate",I("w"),D(0)),I("hi")),
            All(Ex(family,B("beta",Fn(choices,Fn(I("Nat"),I("Label")))),B("cuts",Fn(choices,Call("Frame",I("Configuration"),I("Label")))),
                B("states",Call("Finset",I("Configuration")))),B("n",I("Nat")))),
            B("e",I("Guard")),B("w",Call("List",I("Label"))),B("eta",Fn(I("Nat"),I("Label"))),B("x",Fn(I("Nat"),I("Real"))));
        return Disp(All(Imp(data,result),B("Configuration",I("Type")),B("action",Fn(I("Configuration"),Call("Op",I("Configuration"),I("Color"),I("Label")))),
            B("initialConfiguration",I("Configuration")),B("o",I("Ownership")),B("theta",I("Real")),B("s1",I("Guard")),B("s2",I("Guard")),
            B("P",Call("List",I("Label"))),B("Q",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
            B("U",Fn(I("Bool"),Call("List",I("Label")))),B("V",Call("List",I("Label"))),B("W",Fn(I("Bool"),Call("List",I("Color")))),
            B("L",I("Nat")),B("lo",I("Real")),B("hi",I("Real")),B("a",I("Real")),B("y",I("Real")),B("k",I("Nat"))));
    }

    private static Formula CanonicalLegalReturnHull()
    {
        var u=I("U");var length=I("L");var s=I("s");var i=I("i");var z=I("z");
        var lo=Call("canonicalReturnLo",u,length);var hi=Call("canonicalReturnHi",u,length);
        var word=Call("apply",u,i);var image=Call("compose",word,z);
        Formula Invariant(Formula lower,Formula upper) =>
            All(Imp(And(Call("le",lower,z),Call("le",z,upper)),
                And(Call("le",lower,image),Call("le",image,upper))),B("i",I("Bool")),B("z",I("Real")));
        var data=And(Call("lt",D(0),length),
            All(Equal(Call("length",word),length),B("i",I("Bool"))),
            All(Call("LegalWord",s,s,word),B("i",I("Bool"))));
        var result=And(Call("le",lo,hi),
            Imp(Call("notEqual",Call("apply",u,I("false")),Call("apply",u,I("true"))),Call("lt",lo,hi)),
            All(Imp(And(Call("le",lo,z),Call("le",z,hi)),Call("InSupport",s,z)),B("z",I("Real"))),
            Invariant(lo,hi),
            All(Imp(And(Call("le",I("l"),I("upper")),Invariant(I("l"),I("upper"))),
                And(Call("le",I("l"),lo),Call("le",hi,I("upper")))),B("l",I("Real")),B("upper",I("Real"))),
            new Formula.Logic(Equal(lo,hi),FormulaLogicOperator.Iff,
                Equal(Call("apply",u,I("false")),Call("apply",u,I("true")))),
            And(Call("member",lo,I("coefficientField")),Call("member",hi,I("coefficientField"))));
        return Disp(All(Imp(data,result),B("s",I("Guard")),
            B("U",Fn(I("Bool"),Call("List",I("Label")))),B("L",I("Nat"))));
    }

    private static Formula CanonicalHighFixedFiniteTail()
    {
        var u=I("U");var v=I("V");var length=I("L");var lo=Call("canonicalReturnLo",u,length);var hi=Call("canonicalReturnHi",u,length);
        var lowLo=Call("canonicalReturnLo",v,length);var lowHi=Call("canonicalReturnHi",v,length);
        var theta=Call("familyEndpointBudget",I("P"),I("Q"),I("h"),u,v,I("W"),length);
        var costs=Call("familyEndpointCosts",I("P"),I("Q"),I("h"),u,v,I("W"),length);
        var choices=Call("choiceBlocks",u,I("zs"));var colors=Call("choiceBlocks",I("W"),I("zs"));
        var prefix=Call("append",I("P"),choices);var cs=Call("append",I("h"),colors);
        var alpha=Call("address",Call("append",prefix,I("w")));var record=Call("recordWithTail",I("o"),cs,I("w"));
        var word=Call("apply",u,I("i"));var lowWord=Call("apply",v,I("i"));var colorWord=Call("apply",I("W"),I("i"));
        var data=And(Call("LegalWord",I("G0"),I("s1"),I("P")),Call("LegalWord",I("G0"),I("s2"),I("Q")),
            Equal(Call("length",I("P")),Call("length",I("h"))),Equal(Call("length",I("Q")),Call("length",I("h"))),
            Call("lt",D(0),length),
            All(And(Equal(Call("length",word),length),Equal(Call("length",lowWord),length),
                Call("LegalWord",I("s1"),I("s1"),word),Call("LegalWord",I("s2"),I("s2"),lowWord),
                Equal(Call("length",word),Call("length",colorWord))),B("i",I("Bool"))),
            Call("notEqual",Call("apply",u,I("false")),Call("apply",u,I("true"))));
        var tail=Ex(And(Call("LegalWord",I("s1"),I("e"),I("w")),Call("lt",lo,Call("coordinate",I("w"),D(0))),
            Call("lt",Call("coordinate",I("w"),D(0)),hi),
            All(And(Call("OperationRecord",I("o"),theta,I("closed"),alpha,record),Call("OperationFiniteSource",alpha),
                All(Equal(Call("apply",record,Add(Call("length",cs),I("p"))),
                    Call("observe",I("o"),Call("coordinate",I("w"),I("p")),D(0))),B("p",I("Nat")))),
                B("zs",Call("List",I("Bool"))))),B("e",I("Guard")),B("w",Call("List",I("Label"))));
        var result=And(Call("le",D(0),theta),Equal(Call("length",costs),Add(Mul(D(2),Call("length",I("h"))),Mul(D(4),length))),
            Call("EndpointCertificate",theta,lowLo,lowHi,I("Q"),I("h")),
            All(Call("EndpointCertificate",theta,lowLo,lowHi,lowWord,colorWord),B("i",I("Bool"))),tail);
        return Disp(All(Imp(data,result),B("o",I("Ownership")),B("s1",I("Guard")),B("s2",I("Guard")),
            B("P",Call("List",I("Label"))),B("Q",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
            B("U",Fn(I("Bool"),Call("List",I("Label")))),B("V",Fn(I("Bool"),Call("List",I("Label")))),
            B("W",Fn(I("Bool"),Call("List",I("Color")))),B("L",I("Nat"))));
    }

    private static Formula CanonicalSynchronous()
    {
        var action=I("action");var initial=I("initialConfiguration");var o=I("o");var theta=I("theta");var n=I("n");var z=I("z");
        var lo=Call("canonicalReturnLo",I("U"),I("L"));var hi=Call("canonicalReturnHi",I("U"),I("L"));
        var lowLo=Call("canonicalReturnLo",I("V"),I("L"));var lowHi=Call("canonicalReturnHi",I("V"),I("L"));
        var a=Pow(Call("negate",I("g")),I("L"));
        var v0=Call("apply",I("V"),I("false"));
        var competing=Call("CompetingT",o,theta,I("s2"),I("Q"),v0,I("h"),I("W"));
        var feasible=Call("ifThenElse",Call("lt",D(0),a),
            And(Call("Nonempty",competing),Call("member",lowLo,Call("closure",competing))),Call("member",lowLo,competing));
        var choices=Fn(Call("Fin",n),I("Bool"));var horizon=Add(Call("length",I("P")),Mul(n,I("L")));
        var high=Call("SynchronousHighSource",I("P"),I("U"),z,I("w"));
        var highRecord=Call("recordWithTail",o,Call("synchronousPrefix",I("h"),I("W"),z),I("w"));
        var lowRecord=Call("recordWithOmegaTail",o,Call("synchronousPrefix",I("h"),I("W"),z),I("x"));
        var beta=Call("apply",I("beta"),z);var cut=Call("apply",I("cuts"),z);var stem=Call("take",I("P"),I("k"));
        var ui=Call("apply",I("U"),I("i"));var vi=Call("apply",I("V"),I("i"));var wi=Call("apply",I("W"),I("i"));
        var data=And(Call("LegalWord",I("G0"),I("s1"),I("P")),
            Call("LegalWord",I("G0"),I("s2"),I("Q")),Equal(Call("length",I("P")),Call("length",I("h"))),
            Equal(Call("length",I("Q")),Call("length",I("h"))),Call("lt",D(0),I("L")),
            All(And(Call("LegalWord",I("s1"),I("s1"),ui),Call("LegalWord",I("s2"),I("s2"),vi),
                Equal(Call("length",ui),I("L")),Equal(Call("length",vi),I("L")),
                Equal(Call("length",ui),Call("length",wi))),B("i",I("Bool"))),
            Call("notEqual",Call("apply",I("U"),I("false")),Call("apply",I("U"),I("true"))),
            Call("le",Call("familyEndpointBudget",I("P"),I("Q"),I("h"),I("U"),I("V"),I("W"),I("L")),theta),
            Equal(lowLo,lowHi),feasible,Call("lt",I("k"),Call("length",I("P"))),
            All(Imp(Call("lt",I("p"),I("k")),Equal(Call("getElem",I("P"),I("p")),Call("getElem",I("Q"),I("p")))),B("p",I("Nat"))),
            Call("notEqual",Call("getElem",I("P"),I("k")),Call("getElem",I("Q"),I("k"))),
            Call("ClosedOperationSafety",action,initial,o,theta),Call("ClosedOperationLiveness",action,initial,o,theta),
            Call("ExecutedPostprocessing",action,initial,o,theta));
        var family=And(
            All(And(Call("OperationRecord",o,theta,I("closed"),high,highRecord),Call("OperationFiniteSource",high)),B("z",choices)),
            All(Call("OperationRecord",o,theta,I("closed"),beta,lowRecord),B("z",choices)),
            All(TailPrefix(Call("synchronousPrefix",I("Q"),I("V"),z),beta),B("z",choices)),
            All(Equal(Call("apply",beta,Add(horizon,I("p"))),Call("apply",I("eta"),I("p"))),B("z",choices),B("p",I("Nat"))),
            All(Equal(Call("apply",highRecord,Add(horizon,I("p"))),Call("observe",o,Call("coordinate",I("w"),I("p")),D(0))),B("z",choices),B("p",I("Nat"))),
            Call("Injective",Call("SynchronousHighFamily",I("P"),I("U"),n,I("w"))),
            All(And(Call("Cut",action,initial,Call("front",highRecord,horizon),cut),Call("le",Call("length",Call("output",cut)),I("k")),
                Equal(Call("output",cut),Call("take",stem,Call("length",Call("output",cut)))),Call("IsPrefix",Call("output",cut),stem)),B("z",choices)),
            Call("Injective",Call("cutStateOutputMap",I("cuts"))),
            All(new Formula.Logic(Call("member",I("c"),I("states")),FormulaLogicOperator.Iff,
                Ex(Equal(Call("state",cut),I("c")),B("z",choices))),B("c",I("Configuration"))),
            Call("le",Pow(D(2),n),Mul(Call("card",I("states")),Add(I("k"),D(1)))));
        var result=Ex(And(Call("LegalWord",I("s1"),I("e"),I("w")),Call("lt",lo,Call("coordinate",I("w"),D(0))),
            Call("lt",Call("coordinate",I("w"),D(0)),hi),
            All(Ex(family,B("beta",Fn(choices,Fn(I("Nat"),I("Label")))),B("cuts",Fn(choices,Call("Frame",I("Configuration"),I("Label")))),
                B("states",Call("Finset",I("Configuration")))),B("n",I("Nat")))),
            B("e",I("Guard")),B("w",Call("List",I("Label"))),B("eta",Fn(I("Nat"),I("Label"))),B("x",Fn(I("Nat"),I("Real"))));
        return Disp(All(Imp(data,result),B("Configuration",I("Type")),B("action",Fn(I("Configuration"),Call("Op",I("Configuration"),I("Color"),I("Label")))),
            B("initialConfiguration",I("Configuration")),B("o",I("Ownership")),B("theta",I("Real")),B("s1",I("Guard")),B("s2",I("Guard")),
            B("P",Call("List",I("Label"))),B("Q",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
            B("U",Fn(I("Bool"),Call("List",I("Label")))),B("V",Fn(I("Bool"),Call("List",I("Label")))),B("W",Fn(I("Bool"),Call("List",I("Color")))),
            B("L",I("Nat")),B("k",I("Nat"))));
    }


    private static Formula CanonicalPeriodicEndpoints()
    {
        var u=I("U");var length=I("L");var word=Call("apply",u,I("i"));
        var amin=Call("apply",u,I("imin"));var amax=Call("apply",u,I("imax"));
        var positive=Call("lt",D(0),Pow(Call("negate",I("g")),length));
        var lowWord=Call("ifThenElse",positive,amin,Call("append",amin,amax));
        var highWord=Call("ifThenElse",positive,amax,Call("append",amax,amin));
        var v0=Call("compose",Call("apply",u,I("false")),D(0));
        var v1=Call("compose",Call("apply",u,I("true")),D(0));
        var data=And(Call("lt",D(0),length),All(Equal(Call("length",word),length),B("i",I("Bool"))),
            All(Call("LegalWord",I("s"),I("s"),word),B("i",I("Bool"))));
        var result=Ex(And(Equal(Call("compose",amin,D(0)),Call("min",v0,v1)),
            Equal(Call("compose",amax,D(0)),Call("max",v0,v1)),
            Call("PeriodicTail",I("s"),lowWord,Call("canonicalReturnLo",u,length)),
            Call("PeriodicTail",I("s"),highWord,Call("canonicalReturnHi",u,length))),
            B("imin",I("Bool")),B("imax",I("Bool")));
        return Disp(All(Imp(data,result),B("s",I("Guard")),
            B("U",Fn(I("Bool"),Call("List",I("Label")))),B("L",I("Nat"))));
    }

    private static Formula MarginFamilies => Call("Set", Returns);
    private static Formula MarginEquivalence(Formula a, Formula b) => And(Imp(a, b), Imp(b, a));
    private static Formula UniformMarginScale => Mul(Pow(I("g"), D(2)), Pow(I("chi"), I("K")));
    private static Formula UniformMarginTransitionPremises()
    {
        var q = Sub(I("lam"), Mul(UniformMarginScale, Call("hSide", I("high"))));
        var z = Call("divide", Call("aSide", I("high")),
            Sub(D(1), Mul(I("rho"), Pow(I("chi"), I("K")))));
        var psi = Sub(I("lam"), Mul(UniformMarginScale, z));
        return And(Call("le", D(2), I("K")), Call("lt", q, I("b")),
            Call("lt", I("b"), psi));
    }
    private static Formula UniformMarginFamilySupply(Formula eps) =>
        All(Imp(Call("member", I("execution"), I("family")),
            Call("ActualPairSupply", I("model"), I("o"), Sub(I("b"), eps),
                I("closed"), I("execution"))), B("execution", Returns));
    private static Formula UniformMarginFamilyCap() =>
        All(Imp(Call("member", I("execution"), I("family")),
            All(Imp(Call("member", I("a"), I("execution")),
                Call("le", Call("r", I("a")), I("K"))), B("a", I("Return")))),
            B("execution", Returns));
    private static Formula UniformMarginGapSet =>
        Call("actualFamilyHighGaps", I("model"), I("b"), I("K"), I("family"));
    private static Formula UniformMarginGapLowerBound()
    {
        var premise = And(UniformMarginTransitionPremises(), Call("lt", D(0), I("eps")),
            UniformMarginFamilySupply(I("eps")));
        var conclusion = All(Imp(Call("member", I("gap"), UniformMarginGapSet),
            Call("le", Call("divide", I("eps"), UniformMarginScale), I("gap"))),
            B("gap", I("Real")));
        return Disp(All(Imp(premise, conclusion),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("K", I("Nat")), B("family", MarginFamilies), B("eps", I("Real"))));
    }
    private static Formula UniformMarginIff()
    {
        var uniform = Ex(And(Call("lt", D(0), I("eps")), UniformMarginFamilySupply(I("eps"))),
            B("eps", I("Real")));
        var delta = Call("actualFamilyDelta", I("model"), I("b"), I("K"), I("family"));
        return Disp(All(Imp(And(UniformMarginTransitionPremises(), UniformMarginFamilyCap()),
            MarginEquivalence(uniform, Call("lt", D(0), delta))),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("K", I("Nat")), B("family", MarginFamilies)));
    }

    private static Formula AutomaticMarginG2 => Pow(I("g"), D(2));
    private static Formula AutomaticMarginScale => Mul(AutomaticMarginG2, Pow(I("chi"), I("K")));
    private static Formula AutomaticMarginCost => Call("actualAutomaticCost", I("K"));
    private static Formula AutomaticMarginHighState(Formula prefix) =>
        Call("execute", I("high"), prefix, Call("initial", I("high"), I("model")));
    private static Formula AutomaticMarginActive(Formula exponent, Formula state) =>
        Sub(I("lam"), Mul(Mul(AutomaticMarginG2, Pow(I("chi"), exponent)), state));
    private static Formula AutomaticMarginAnchorCost =>
        Sub(I("lam"), Mul(Mul(AutomaticMarginG2, I("chi")), Call("xSide", I("high"))));
    private static Formula AutomaticMarginQ => Sub(I("lam"), Mul(AutomaticMarginScale, Call("hSide", I("high"))));
    private static Formula AutomaticMarginPsi => Sub(I("lam"), Mul(AutomaticMarginScale,
        Call("divide", Call("aSide", I("high")),
            Sub(D(1), Mul(I("rho"), Pow(I("chi"), I("K")))))));
    private static Formula AutomaticMarginCap(Formula xs) =>
        All(Imp(Call("member", I("a"), xs), Call("le", Call("r", I("a")), I("K"))),
            B("a", I("Return")));
    private static Formula AutomaticMarginStrictCostSupplier()
    {
        var stem = Sub(I("lam"), Mul(Mul(AutomaticMarginG2, I("chi")), AutomaticMarginHighState(I("execution"))));
        var costs = And(Call("lt", stem, I("budget")),
            Imp(Equal(I("model"), I("anchored")), Call("lt", AutomaticMarginAnchorCost, I("budget"))),
            Call("StrictControl", I("high"), I("budget"), I("execution"),
                Call("initial", I("high"), I("model"))));
        return Disp(All(Imp(Call("lt", Sub(I("lam"), I("rho")), I("budget")),
            MarginEquivalence(Call("ActualPairSupply", I("model"), I("o"), I("budget"),
                I("strict"), I("execution")), costs)),
            B("model", I("Model")), B("o", I("Ownership")), B("budget", I("Real")),
            B("execution", Returns)));
    }
    private static Formula AutomaticMarginEnvelope()
    {
        var domain = Call("lt", Call("aSide", I("high")), I("D"));
        var stem = Sub(I("lam"), Mul(Mul(AutomaticMarginG2, I("chi")), I("D")));
        var conclusion = And(Call("lt", AutomaticMarginCost, AutomaticMarginQ),
            Call("le", Sub(I("lam"), I("rho")), AutomaticMarginCost), Call("le", AutomaticMarginAnchorCost, AutomaticMarginCost),
            All(Imp(domain, Call("lt", stem, AutomaticMarginCost)), B("D", I("Real"))),
            All(Imp(And(Call("lt", I("r"), I("K")), domain),
                Call("lt", AutomaticMarginActive(I("r"), I("D")), AutomaticMarginCost)),
                B("r", I("Nat")), B("D", I("Real"))));
        return Disp(All(Imp(Call("le", D(2), I("K")), conclusion), B("K", I("Nat"))));
    }
    private static Formula AutomaticMarginCappedSupplier()
    {
        var split = Equal(I("execution"), Call("append", I("before"),
            Call("cons", I("a"), I("after"))));
        var high = All(Imp(And(split, Equal(Call("r", I("a")), I("K"))),
            Call("lt", AutomaticMarginActive(I("K"), AutomaticMarginHighState(I("before"))), I("budget"))),
            B("before", Returns), B("a", I("Return")), B("after", Returns));
        return Disp(All(Imp(And(Call("le", D(2), I("K")),
            Call("lt", AutomaticMarginCost, I("budget")), AutomaticMarginCap(I("execution")), high),
            Call("ActualPairSupply", I("model"), I("o"), I("budget"),
                I("strict"), I("execution"))),
            B("model", I("Model")), B("o", I("Ownership")), B("K", I("Nat")),
            B("budget", I("Real")), B("execution", Returns)));
    }
    private static Formula AutomaticMarginExactSupply()
    {
        var delta = Call("actualFamilyDelta", I("model"), I("b"), I("K"), I("family"));
        var eps = Call("actualExactFamilyMargin", I("model"), I("b"), I("K"), I("family"));
        var cap = All(Imp(Call("member", I("execution"), I("family")), AutomaticMarginCap(I("execution"))),
            B("execution", Returns));
        var supplied = All(Imp(Call("member", I("execution"), I("family")),
            Call("ActualPairSupply", I("model"), I("o"), Sub(I("b"), eps),
                I("strict"), I("execution"))), B("execution", Returns));
        return Disp(All(Imp(And(Call("le", D(2), I("K")), Call("lt", AutomaticMarginQ, I("b")),
            Call("lt", I("b"), AutomaticMarginPsi), cap, Call("lt", D(0), delta)),
            And(Call("lt", D(0), eps), supplied)),
            B("model", I("Model")), B("o", I("Ownership")), B("b", I("Real")),
            B("K", I("Nat")), B("family", MarginFamilies)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-canonical-legal-return-hull"),
                DeclarationHandle.Create(Prefix+"canonical_legal_return_hull"),
                H("Actual legal returns determine their canonical hull"),
                StatementSource.FromAuthor(CanonicalLegalReturnHull()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write A(i)=compose(U(i),0), a=(-g)^L, Amin=min(A(false),A(true)), and Amax=max(A(false),A(true)). The common return length L is positive. canonicalReturnLo and canonicalReturnHi use (Amin/(1-a),Amax/(1-a)) when a>0, and ((Amin+a*Amax)/(1-a^2),(Amax+a*Amin)/(1-a^2)) when a<0. The literal slope has nonzero absolute value less than one. The width is respectively (Amax-Amin)/(1-a) or (Amax-Amin)/(1+a).")),
                    Paragraph(Text("Both words return legally from s to s. The displayed interval is nonempty, lies in the actual guard support, is invariant under each full return, and is contained in every nonempty invariant closed interval [l,upper]. Distinct equal-length words have distinct zero-tail scalar values: all finite suffixes at zero lie strictly inside their actual guard supports, and root branch interiors from one guard are disjoint. Induction then recovers the labels and full words from equal scalars. Literal return difference therefore gives strict hull width. The notEqual predicate in the displayed statement denotes literal inequality.")),
                    Paragraph(Text("The statement permits equal words and a singleton hull. It does not identify the interval with the attractor. The singleton-hull equivalence is literal word equality. coefficientField is the intersection of all real subfields containing t, hence the original Q(t). Both computed endpoints belong to this field. The specified periodic endpoint addresses are supplied separately by canonical_periodic_endpoints."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-canonical-high-fixed-finite-tail"),
                DeclarationHandle.Create(Prefix+"canonical_high_fixed_finite_tail"),
                H("The canonical high hull supplies one finite tail for all histories"),
                StatementSource.FromAuthor(CanonicalHighFixedFiniteTail()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two actual high return words differ literally and have the same positive length. The hull endpoints are exactly canonicalReturnLo(U,L) and canonicalReturnHi(U,L). Their width, support and invariance follow from those legal returns. familyEndpointCosts concatenates the indexed endpoint costs for P,h on the U hull, Q,h on the V hull, and each U(i),W(i) and V(i),W(i) pair. Each entry is the maximum of the two endpoint distances max(cut(c)-x,0,x-cut(c+1)) to the closed color interval. There are exactly 2*length(h)+4*L entries. familyEndpointBudget is their fold by max starting at zero. The legal supports and this one computed maximum derive every supported EndpointCertificate; no certificate is supplied as a premise.")),
                    Paragraph(Text("A single finite legal word w is chosen before every finite Bool choice list zs. It lies strictly inside the canonical hull. The actual source is address((P++choiceBlocks(U,zs))++w), and its record is recordWithTail(o,h++choiceBlocks(W,zs),w). The original finite-tail theorem supplies the closed-budget actual record, eventual L0 source and literal zero-error future of this same fixed tail. Empty stems and the empty choice list are included. The finite endpoint maximum is computed and supplies the high actual family. Its necessity for arbitrary fixed tails, including tails outside the hull, remains unproved. The low certificates are closed constraints and do not by themselves settle actual low endpoint ownership. This statement does not settle the complete original theorem or a common positive margin over unbounded histories."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-canonical-synchronous-common-stem"),
                DeclarationHandle.Create(Prefix+"canonical_synchronous_common_stem"),
                H("Canonical legal families supply the arbitrary common-stem count"),
                StatementSource.FromAuthor(CanonicalSynchronous()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("U and V are the two actual Bool-indexed legal return families of the same positive length L. U(false) differs from U(true). The high hull is computed from U. Equality of the two canonical V endpoints is equivalent to literal V(false)=V(true), so the common competing return and its fixed point are derived. The actual CompetingT tests every Q suffix and both W color words. Its signed feasibility test uses the canonical low endpoint and a=(-g)^L; positive slope retains a closure limit and negative slope requires actual membership.")),
                    Paragraph(Text("The finite endpoint budget familyEndpointBudget(P,Q,h,U,V,W,L) is at most theta. Its exact indexed costs derive the observed high stem and return certificates. The nonnegative computed budget also derives theta nonnegativity. Minimum-budget necessity for arbitrary fixed tails remains unproved. SameStem compares P and Q at every position below k, and DifferentStem compares their labels at k<P.length. getElem denotes literal list extraction. ClosedOperationSafety, ClosedOperationLiveness and ExecutedPostprocessing retain their original actual-record contracts. SynchronousHighSource(P,U,z,w)=address(synchronousPrefix(P,U,z)++w); SynchronousHighFamily is this map on Fin(n)->Bool, and cutStateOutputMap(z)=((cuts(z)).state,(cuts(z)).output).")),
                    Paragraph(Text("One finite high tail and one legal competing Omega tail are fixed before every n. The sources have the actual prescribed prefixes, all histories are acquired on those sources, the high future is the single literal zero-error tail, and literal block extraction gives source injection. Existing common-stem processing then supplies actual cuts and 2^n<=states.card*(k+1), including n=0 and arbitrary supported k. The construction computes the finite endpoint maximum and uses its sufficient bound. It does not derive minimum-budget necessity, the optional piece condition or the auxiliary SFT scope."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-canonical-periodic-endpoints"),
                DeclarationHandle.Create(Prefix+"canonical_periodic_endpoints"),
                H("Extremal literal return blocks encode the canonical endpoints"),
                StatementSource.FromAuthor(CanonicalPeriodicEndpoints()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("imin and imax attain the minimum and maximum of the two actual zero-tail translations. For positive signed slope the lower endpoint repeats U(imin), and the upper endpoint repeats U(imax). For negative slope the respective repeating words are U(imin)++U(imax) and U(imax)++U(imin). Their lengths are L or 2L, so the block periods are one or at most two, including equal translations.")),
                    Paragraph(Text("PeriodicTail(s,w,z) means there are label, scalar and guard sequences a,x,path with path(0)=s and x(0)=z, every literal edge legal, every coordinate in that guard's support, and x(p)=branch(a(p),x(p+1)). At each p<length(w), a(p)=w[p]. For every p the label, scalar and guard at p+length(w) equal their values at p. The proof splices one legal block onto a supported tail and repeats the actual finite block itinerary, using the fixed endpoint coordinate and return guard to verify the joining edge. It does not infer this periodicity from an arbitrary lawful_tail witness or claim a finite-D representative for either endpoint."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-lawful-tail"),DeclarationHandle.Create(Prefix+"lawful_tail"),
                H("Every supported scalar has one legal itinerary"),StatementSource.FromAuthor(TailLawful()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The closed branch images cover [-1,phi] at G0 and [-1,t] at G1. The inverse branch (shift(label)-z)/g remains in its next guard support. Iterating supported guard-scalar pairs gives one label sequence, one coordinate sequence and one legal guard path with the requested scalar. Shared branch endpoints remain legal."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-finite-approximation"),DeclarationHandle.Create(Prefix+"finite_approximation"),
                H("Finite legal zero tails approximate every supported scalar"),StatementSource.FromAuthor(TailApproximation()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Truncate the same itinerary after n labels. The exact remaining-coordinate error is (-g)^n*x(n), whose absolute value is at most phi*g^n. Geometric convergence gives every positive tolerance. This density concerns the full guard support; it does not identify that interval with a two-return attractor."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-finite-tail-interior"),DeclarationHandle.Create(Prefix+"finite_tail_interior"),
                H("A finite tail in a supported interval interior"),StatementSource.FromAuthor(TailInterior()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A midpoint approximation within half the interval width yields a finite legal word whose zero-tail scalar lies strictly between lo and hi. coordinateSequence(w)(p)=coordinate(w,p). The full eventually-L0 address and its entire legal supported coordinate path are retained, for either initial guard."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-prepend-legal-tail"),DeclarationHandle.Create(Prefix+"prepend_legal_tail"),
                H("Splicing one fixed legal coordinate tail"),StatementSource.FromAuthor(TailPrepend()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("TailPath(s,a,x,path) means that path starts at s, every label follows nextGuard, every scalar lies in its corresponding support, and every affine recurrence holds. A legal finite prefix prepends exactly its labels and composition value. Both shifted futures are exact, including the recurrence at the splice boundary."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-cell-flag-interval"),DeclarationHandle.Create(Prefix+"cell_flag_interval"),
                H("Exact color cells and all five endpoint flags"),StatementSource.FromAuthor(TailColor("cell")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("FlagInterval(lo,hi,left,right,z) is lo<=z<=hi with z=lo implying left and z=hi implying right. lowerOwned is true at color zero and otherwise uses the corresponding true flag; upperOwned is true at color five and otherwise uses the corresponding false flag. These are exactly the original Cell boundaries."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-owned-color-interval"),DeclarationHandle.Create(Prefix+"owned_color_interval"),
                H("Closed error dilation with actual endpoint ownership"),StatementSource.FromAuthor(TailColor("interval")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("OwnedColor(o,theta,c,z) requires z in G0 support and a target u in the actual Cell(o,c) with abs(z-u)<=theta. Dilation shifts the two cell endpoints by theta and retains their original ownership. Support is intersected separately, so clipping an expanded interval does not transfer an unrelated ownership flag to a new boundary. At theta zero the target is z itself."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-owned-color-error"),DeclarationHandle.Create(Prefix+"owned_color_error"),
                H("Attainable colors are exact observe error outcomes"),StatementSource.FromAuthor(TailColor("error")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For supported z, clipping z+error changes its distance from z by at most abs(error). Conversely a supported target u is fixed by clip and is obtained with error=u-z. This proves both directions of the actual observe relation, including every ownership flag."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-owned-color-connected"),DeclarationHandle.Create(Prefix+"owned_color_ordConnected"),
                H("Actual attainable color sets are intervals"),StatementSource.FromAuthor(TailColor("connected")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("setOfOwnedColor(o,theta,c) is the set of real z satisfying OwnedColor(o,theta,c,z). Its supported flagged interval is order-connected, including empty sets and excluded endpoints."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-competing-t-connected"),DeclarationHandle.Create(Prefix+"competingT_ordConnected"),
                H("The actual competing-tail intersection is an interval"),StatementSource.FromAuthor(TailCompeting("interval")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CompetingT is the intersection of the terminal guard support, every actual Q-suffix color constraint for r<h.length, and every V-suffix constraint for each of the two W words. Affine preimages preserve order-connectedness for either slope sign. No terminal color test is added."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-competing-t-actual"),DeclarationHandle.Create(Prefix+"competingT_mem_actual"),
                H("Concrete tail membership and actual slot errors"),StatementSource.FromAuthor(TailCompeting("actual")),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Legal Q and V words transport support through every suffix. Membership in CompetingT is exactly supported terminal membership and the closed BlockSupply conditions for the stem and both return-color choices."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-certificate-actual-slots"),DeclarationHandle.Create(Prefix+"certificate_actual_slots"),
                H("Finite endpoint costs supply every interior slot"),StatementSource.FromAuthor(TailCertificate()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("EndpointCertificate gives supported images of lo and hi at each departure suffix and bounds max(cut(c)-z,0,z-cut(c+1)) by theta at each image. A nonzero literal suffix slope sends an interior scalar strictly between those two endpoint images. This yields actual ownership-sensitive error witnesses at theta, including theta zero."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-fixed-finite-all-histories"),DeclarationHandle.Create(Prefix+"fixed_finite_tail_all_histories"),
                H("One finite tail supplies all high histories"),StatementSource.FromAuthor(TailHigh()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The numerical hull is nondegenerate, supported and invariant under both legal returns; its stem and return endpoint costs satisfy EndpointCertificate. One finite word w is selected before all Bool choice lists. Each source is address((P++choiceBlocks(R,zs))++w), with the prescribed h++choiceBlocks(W,zs) past followed by the literal zero-error coordinate future of w. Errors are chosen on this same source and are zero after the past. Empty stems and histories remain included. A common positive margin over unbounded histories is not asserted."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-fixed-omega-all-histories"),DeclarationHandle.Create(Prefix+"fixed_omega_tail_all_histories"),
                H("One lawful Omega tail supplies all rival histories"),StatementSource.FromAuthor(TailLow()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("constantWordFamily(V)(i)=V and composeMap(V)(z)=compose(V,z). The actual fixed-point and slope equations identify the centered affine return. Positive-slope feasibility uses nonempty CompetingT and closure membership of its fixed point; negative-slope feasibility uses actual CompetingT membership. One supported scalar is lifted to one legal tail before all histories. Each finite choice sees only the remaining number of identical V returns, while both distinct W color choices remain in every orbit test. The full CompetingT orbit condition is equivalent to supported terminal coordinates and BlockSupply for every finite Q-prefixed history; the reverse direction extracts Q and both W blocks from those same histories. Every record uses its own actual finite errors and the unchanged zero-error tail future."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-synchronous-common-stem"),DeclarationHandle.Create(Prefix+"original_synchronous_common_stem"),
                H("Literal source construction at every first stem disagreement"),StatementSource.FromAuthor(TailSynchronous()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("SynchronousSourceData expands as follows: theta>=0; P and Q are legal G0-to-s1/s2 stems with the same length as h; both U returns and the shared V return are legal and have common positive length L, equal to each W length; U(false) differs from U(true). The supported high hull [lo,hi] has positive width and is invariant under U, with the finite EndpointCertificate for P and each U/W pair. The actual V slope a=(-g)^length(V) is nonzero and lies between -1 and 1, compose(V,y)=y, and the sign-sensitive CompetingT feasibility holds. The stems agree before k<length(P) and differ at k. ClosedOperationSafety and ClosedOperationLiveness quantify all original closed OperationRecords and all primitive Runs; liveness is positionwise on eventual-L0 sources. ExecutedPostprocessing is a finite Drain only after actual executed acquisitions.")),Paragraph(Text("SynchronousHighSource(P,U,z,w)=address(synchronousPrefix(P,U,z)++w), and synchronousPrefix(P,U,z)=P++choiceBlocks(U,List.ofFn(z)); SynchronousHighFamily is this source map. The observation horizon is length(P)+nL. Literal block extraction proves its injection from U(false)!=U(true), without a history-injection premise. Independent lawful zero-error [L0] and [L3] records derive startup, preserving arbitrary k in the target family. cutStateOutputMap(cuts)(z) is the pair of readable state and output at that cut. The actual common-stem theorem gives exactly 2^n<=card(states)*(k+1), with n=0 included. Deriving the canonical hull and its nondegeneracy, the original singleton-return reduction and the necessity of the canonical theta maximum remains additional work; optional original return pieces retain their own selection and whole-prefix conditions."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-competing-tail-orbit-criterion"),DeclarationHandle.Create(Prefix+"competing_tail_orbit_criterion"),
                H("Endpoint-sensitive scalar competing-tail orbits"),StatementSource.FromAuthor(TailOrbit()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CenteredAffine(y,a)(x)=y+a(x-y), and iterateApply(f,n,x)=f^[n](x). T is any order-connected real set, including empty and singleton intervals. For 0<a<1 the full orbit condition is x in T and y in closure(T); membership of y itself is unnecessary. For -1<a<0 it is x in T and f(x) in T; these two actual members also force y in T, and this is equivalent to a nonempty feasible orbit set. Positive iterates converge to y and lie strictly between the initial point and y; negative iterates remain in the closed segment between x and f(x). Actual open and closed endpoint membership is retained.")),
                    Paragraph(Text("This is the scalar interval part of the original39.5 criterion. The concrete owned-color intersection and fixed-tail constructions connect this scalar condition to actual legal source records under their explicit hull and return-map data. An optional original-piece restriction requires a member of the feasible orbit set in that piece and is imposed only when present in the family. Canonical hull nondegeneracy, singleton-return reduction, canonical budget necessity and optional whole-prefix piece conditions remain separate original obligations."))),DescribeRole.Theorem),

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
            Describe.Lean(DescribeId.Create("fib-actual-strict-cost-supply"),
                DeclarationHandle.Create(Prefix + "actual_strict_cost_supply"),
                H("Complete actual source costs above the nonactive-slot bound"),
                StatementSource.FromAuthor(AutomaticMarginStrictCostSupplier()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This supplier exposes the existing whole-source cost construction with its actual lower-budget hypothesis budget>lam-rho. It is the same fixed source, history, external block order and literal tail used by the strict record theorem. StrictControl recursively tests lam-g^2*chi^r*D at each actual return start. The stem tests chi times the final whole-list state, and the paid anchor tests chi times X_H, not its output Y_H.")),
                    Paragraph(Text("For a six-block input D<h_j, the nth outer input is h_j-rho^n*(h_j-D). Its active cost minus the next active cost is g^2*rho^n*(1-rho)*(h_j-D)>0. The local activeCostDrops proof is consumed by the bound for arbitrary repetitions. literal_full_slot_readout supplies every six-slot and twenty-slot departure above lam-rho. High/low ordering transports the high costs to the actual paired low source, and pairErrors chooses the finite errors and appends the unchanged zero-error future."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-automatic-cost-envelope"),
                DeclarationHandle.Create(Prefix + "actual_automatic_cost_envelope"),
                H("The exact three-term automatic bound"),
                StatementSource.FromAuthor(AutomaticMarginEnvelope()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("actualAutomaticCost(K)=max(max(lam-g^2*chi*xSide(high),lam-g^2*chi^(K-1)*aSide(high)),lam-g^6). This is precisely C_auto of the original display. The three entries are the fixed-anchor cost Theta_1, the low-return and stem envelope, and the nonactive-slot bound. For K>=2, chi*h_H<A_H and X_H>A_H give the first two strict comparisons with q_K; g^2*chi^K*h_H<g^6 gives the third. The natural subtraction in K-1 is used only under K>=2.")),
                    Paragraph(Text("Every actual complete state lies above A_H. A stem uses chi*D; every r<K return uses chi^r*D>=chi^(K-1)*D. These inputs strictly exceed chi^(K-1)*A_H and their active costs are below C_auto. The stated scalar bounds are consumed by the capped supplier and the exact-margin theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-capped-strict-supply-of-high-costs"),
                DeclarationHandle.Create(Prefix + "actual_capped_strict_supply_of_high_costs"),
                H("Capped complete sources at every budget above C_auto"),
                StatementSource.FromAuthor(AutomaticMarginCappedSupplier()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only budget>C_auto, the literal cap r<=K, and the active-cost test at each actual r=K position are needed. There is no q_K<budget premise. The exact split before++(a::after) identifies the actual prefix state. Automatic slots pass by the envelope; high positions pass by the supplied strict cost. The resulting ActualPairSupply contains the whole prescribed paired sources and original zero-error futures for arbitrary ownership flags."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-exact-uniform-family-margin"),
                DeclarationHandle.Create(Prefix + "actual_exact_uniform_family_margin"),
                H("The original C_auto-based numerical margin for the whole family"),
                StatementSource.FromAuthor(AutomaticMarginExactSupply()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write G=actualFamilyHighGaps(model,b,K,family), Delta=actualFamilyDelta(model,b,K,family), and c=g^2*chi^K. If G is nonempty, actualExactFamilyMargin is min(b-C_auto,c*Delta.toReal)/2. If G is empty, it is (b-C_auto)/2. Delta is the signed EReal infimum over every actual high position; in the nonempty positive case the proof establishes Delta<top and Delta!=bottom before using toReal. No attained minimum is assumed.")),
                    Paragraph(Text("The same positive epsilon is fixed before all lists and both source sides. In the nonempty case every high gap is at least Delta.toReal. Taking half the displayed minimum leaves strict budget room both above C_auto and above every high active cost. With no high returns the latter condition is vacuous, so the separate original formula applies even if the new budget is below q_K. All slots satisfy strict error bound b-epsilon, which also gives the requested closed bound with that exact epsilon, and the original literal futures have zero error.")),
                    Paragraph(Text("The family remains an arbitrary set of finite return lists, with unbounded exponents m, histories, list depths and weights. Both actual models and every ownership assignment remain parameters. The earlier full-family iff and exact necessary epsilon lower bound are retained. The ownership-sensitive closed high-guard law is unchanged. No original13, original39.4, original39.5 or original39.7 goal is changed or declared settled."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-uniform-margin-gap-lower-bound"),
                DeclarationHandle.Create(Prefix + "actual_uniform_margin_gap_lower_bound"),
                H("The supplied epsilon bounds every actual high-return gap"),
                StatementSource.FromAuthor(UniformMarginGapLowerBound()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("actualFamilyHighGaps(model,b,K,family) is the real set of execute(high,before,initial(high,model))-(lam-b)/g^2/chi^K, for every literal decomposition before++(a::after) belonging to family with a.r=K. Each decomposition selects the actual state before that return. This includes every high-return position of every family list; no return-length, list-depth, weight or family-cardinality bound is imposed.")),
                    Paragraph(Text("The same supplied epsilon is used for every record and both sides. Its closed error budget b-eps is not required as an extra premise to belong to the transition interval. If a control cost exceeded that budget, the complete-boundary inequality D<h_H would permit an intermediate budget strictly above q_K and strictly below both b and that cost. Monotonicity preserves the identical errors, observations and literal futures at that intermediate budget. The existing ownership-sensitive closed guard then contradicts its control cost. Thus the original eps, without shrinking, gives gap>=eps/(g^2*chi^K). This bound is consumed by the family equivalence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fib-actual-uniform-family-margin-iff"),
                DeclarationHandle.Create(Prefix + "actual_uniform_family_margin_iff"),
                H("Positive extended-real infimum is equivalent to one family margin"),
                StatementSource.FromAuthor(UniformMarginIff()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("actualFamilyDelta is sInf of the image of actualFamilyHighGaps under the signed real inclusion into EReal. Negative gaps are preserved. The empty high-return set has infimum top, namely positive infinity. The family itself may be empty, and a nonempty family may have no high return. No compactness, attained minimum, finite codebook or common weight is assumed.")),
                    Paragraph(Text("ActualUniformFamilyMargin means there exists one real eps>0 such that every execution in family satisfies ActualPairSupply(model,o,b-eps,closed,execution). Unfolding that existing supply predicate, every side has its own error function bounded by b-eps at all natural positions, reads every departure of the complete history from the same sourcePrefix, is zero at and beyond the history length, and gives the original tailPrefix zero-error readout after the observedPrefix. The stem, paid anchor, all repetitions, literal external block order and unchanged eventual-empty tail therefore remain those of the existing source construction.")),
                    Paragraph(Text("The reverse implication directly consumes actual_exact_uniform_family_margin. It chooses the original C_auto-based epsilon for the nonempty or empty actual high-gap set, then uses those same whole-source witnesses with the closed b-eps bound. The exact sufficient-margin supplier remains valid even when that new budget is below q_K. This works for either original or anchored model and every ownership assignment. Individual-record margins and ownership-sensitive equality at the original closed budget remain the separate existing statements.")),
                    Paragraph(Text("The forward implication consumes the exact necessary bound for the original supplied epsilon; the reverse implication consumes the precise two-branch C_auto margin. Together they retain the whole-family infimum criterion. The original13, original39.4, original39.5 and original39.7 targets retain their existing scope."))),
                DescribeRole.Theorem),
            Paragraph(Text("The classwise deletion and finite exact-weight cardinality applications are separate from the retained run and actual-membership declarations. The finite configuration lower bound uses full actual supply, safety and positionwise liveness. A lower or upper occurrence map alone does not supply a common positive margin for an infinite family.")))));
}
