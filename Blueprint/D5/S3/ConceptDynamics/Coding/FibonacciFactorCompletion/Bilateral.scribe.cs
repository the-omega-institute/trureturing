using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class BilateralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Bilateral.";
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

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Fibonacci return lists have unique execution-word and color-history decodings. Bilateral letter pasts determine a unique bounded state, terminal-u words have unique positive-run decompositions, and independently occurring runs inherit their exact return guards.",
        H("Execution parsing, bilateral past states and return guards"),
        Blocks(
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
                    Paragraph(Text("Matching-past stability gives continuity in the product of the discrete letter spaces. AuxiliaryLanguage forbids K+1 consecutive c letters and checks chi^(K-1)*d before a current c whose preceding K-1 letters are c. For K at least one and every real d, the all-u sequence belongs to this closed compact language. States commute with every integer shift, where shift(omega,j)(n)=omega(n+j), and membership is invariant under those shifts. This language is defined by the independent letter conditions and is not a completion image or an actual literal source."))),
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
                Blocks(Paragraph(Text("The bilateral sequence independently belongs to AuxiliaryLanguage. Its letters agree with the prescribed complete execution word at every position except that the final u may have been appended as a terminal fill. All c letters must still agree. Each run inherits the cap from the original forbidden K+1 c letters. At a run of length K, the original state before its last c is chi^(K-1) times its run-start state, so the independent before-Kth-c guard yields the weak return guard. When another return follows, every intervening u is an original occurrence letter and the exact transition law aligns its next start. No state alignment is claimed across an appended terminal u."))), DescribeRole.Theorem))));
}
