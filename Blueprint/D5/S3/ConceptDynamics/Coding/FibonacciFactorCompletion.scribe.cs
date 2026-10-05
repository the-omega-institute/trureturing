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


    private static Formula JointPrefixConfigurationCardinality()
    {
        Formula Apply(Formula f, Formula at) => Call("apply", f, at);
        Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
        var family = I("family"); var xs = I("xs"); var k = I("k");
        var configuration = I("configuration"); var emittedPrefix = I("emittedPrefix");
        var commonStem = I("commonStem");
        var prefixSet = Call("commonStemPrefixes", commonStem, k);
        var joint = Call("pair", Apply(configuration, xs), Apply(emittedPrefix, xs));
        var prefixMembership = All(Imp(Call("member", xs, family),
            Call("member", Apply(emittedPrefix, xs), prefixSet)), B("xs", Returns));
        var premise = And(Call("InjectiveOn", joint, family), prefixMembership);
        var conclusion = Call("le", Call("card", family),
            Mul(Call("card", Call("image", family, configuration)), Add(k, D(1))));
        return Disp(All(Imp(premise, conclusion),
            B("Configuration", I("Type")),
            B("family", Call("Finset", Returns)),
            B("configuration", new Formula.TypeArrow(Returns, I("Configuration"))),
            B("emittedPrefix", new Formula.TypeArrow(Returns, Call("List", I("Label")))),
            B("commonStem", Call("List", I("Label"))), B("k", I("Nat"))));
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

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
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
            Describe.Lean(DescribeId.Create("fib-joint-prefix-configuration-cardinality"),
                DeclarationHandle.Create(Prefix + "joint_prefix_configuration_cardinality"),
                H("Joint configuration and common-stem prefix cardinality"),
                StatementSource.FromAuthor(JointPrefixConfigurationCardinality()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the family-to-(complete configuration, emitted prefix) map is injective and every emitted prefix belongs to the prefixes of one common stem through position k, then the family has at most (k+1) times as many reached configurations. The prefix set is constructed once from the common stem, so the factor is proved by a finite image cardinality bound. This relation is the arbitrary-k bridge: an individual output-length bound without a shared stem does not supply it. The emitted prefix remains a joint counting coordinate; it is not counted as readable memory."))), DescribeRole.Theorem),
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
