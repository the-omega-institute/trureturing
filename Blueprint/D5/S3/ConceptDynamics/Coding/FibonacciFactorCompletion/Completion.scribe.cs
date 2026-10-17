using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class CompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/Completion.";
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

    private static Formula SourceAddressInjection()
    {
        var j = I("j"); var model = I("model"); var xs = I("xs"); var ys = I("ys");
        var premise = And(Equal(Call("listWeight", xs), Call("listWeight", ys)),
            Equal(Call("source", j, model, xs), Call("source", j, model, ys)));
        return Disp(All(new Formula.Logic(premise, FormulaLogicOperator.Implies, Equal(xs, ys)),
            B("j", I("Side")), B("model", I("Model")), B("xs", Returns), B("ys", Returns)));
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


    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-auxiliary-lower-padding"),
                DeclarationHandle.Create(Prefix + "auxiliary_lower_padding"),
                H("Literal auxiliary padding of weak complete actual lists"),
                StatementSource.FromAuthor(LowerPadding()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For K at least one, any real guard d and either actual initial model, a weakly guarded complete return list has its exact execution word at the origin of uPadding. This sequence equals that finite word at nonnegative positions inside it, and equals u at every other integer position. Its infinite-past state at zero is h_H. At every complete return boundary its state strictly exceeds the state of the original actual recurrence. Every c position is located in an original return; the intervening positive u runs prevent a K-letter guard from crossing a return boundary. The cap excludes K+1 consecutive c letters, and the weak actual guard transfers to the independent before-Kth-c auxiliary guard. The exact finite word occurs at zero and is an AuxiliaryFactor, with weight equal to listWeight. Combined directly with the existing complete execution parser, this supplies an injection of exact-weight weak complete lists into distinct occurrence factors. Empty lists are included. The auxiliary u tails do not replace either original eventually-empty literal source or its zero-error future. castInt is the natural-to-integer inclusion."))),
                DescribeRole.Theorem),
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
                Blocks(Paragraph(Text("For either actual side and either model, two return lists of the same variable weight have equal full eventually-empty source addresses only if the lists are equal. Equality of addresses determines the finite observed prefixes because their original lengths coincide. Removing the same stem and paid anchor leaves equal external label words. On the high side U and C have different second labels; on the low side V and C have different first labels. The label-block encoding is therefore uniquely recoverable. Reversing the execution-letter order preserves the letters inside each original block, and the existing complete execution parser recovers the return list. The two literal tails remain unchanged. This is a statement about literal addresses; it does not assert injectivity of the scalar coordinate or establish an asymptotic rate."))), DescribeRole.Theorem))));
}
