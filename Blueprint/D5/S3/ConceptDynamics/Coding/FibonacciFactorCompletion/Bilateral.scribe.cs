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

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
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
                    Paragraph(Text("Matching-past stability gives continuity in the product of the discrete letter spaces. AuxiliaryLanguage forbids K+1 consecutive c letters and checks chi^(K-1)*d before a current c whose preceding K-1 letters are c. For K at least one and every real d, the all-u sequence belongs to this closed compact language. States commute with every integer shift, where shift(omega,j)(n)=omega(n+j), and membership is invariant under those shifts. AuxiliaryFactor is defined by an actual occurrence in a sequence satisfying those independent conditions; neither object is a completion image or an actual literal source."))),
                DescribeRole.Theorem))));
}
