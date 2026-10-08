using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Antipowers;

internal sealed class GargFibonacciPrefixAntipowerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Antipowers/GargFibonacciPrefixAntipower.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Words/garg2021antipowers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first F_n−1 blocks of length F_n/2+F_{n−1} in the Fibonacci word are distinct whenever F_n is even.",
        H("Garg's Fibonacci Prefix Antipower"),
        Blocks(
            Node("garg-digit", "Binary letters", "digit", DigitFormula(),
                "Boolean true in goldenWord denotes the source's letter 0; false denotes 1. "
                    + "The binary alphabet is Fin 2.", DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source)),
            Node("garg-prefixes", "Finite Fibonacci prefixes", "S", PrefixFormula(),
                "The Fibonacci word begins with 0 and is fixed by the morphism 0 ↦ 01, 1 ↦ 0. "
                    + "The recursive prefixes begin [0] and [0,1], followed by concatenation "
                    + "of the previous two prefixes in that order. The plus-plus symbol is List append.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("garg-word", "Infinite Fibonacci word", "fibW", WordFormula(),
                "The ith letter is read from prefix S(i). These prefixes are compatible, and "
                    + "their lengths exceed i. List indexing includes the proved bound. "
                    + "The proof identifies this limit with digit(goldenWord(i)), so the "
                    + "source's initial letter and letter correspondence are preserved.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("garg-length", "The specified block length", "blockLength", LengthFormula(),
                "Nat.fib has F_0=0 and F_1=F_2=1. Nat.div denotes floor division on naturals; "
                    + "it is exact division by 2 for the even Fibonacci numbers in the claim. "
                    + "Natural subtraction is truncated subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(DescribeId.Create("garg-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"), H("Conjecture 18"),
                StatementSource.FromAuthor(ClaimFormula()), AssessedProvenance.FromLiterature(Source),
                Blocks(SourceQuotation(), AntipowerQuotation(), Paragraph(Text(
                    "For every n ≥ 1 with Nat.fib(n) even, the indices i and j range over the "
                        + "first Nat.fib(n)−1 blocks. Each block is a function Fin(blockLength(n)) → Fin 2, "
                        + "starting at index i·blockLength(n) or j·blockLength(n). Distinct indices "
                        + "give distinct functions. Thus the concatenation is a prefix antipower."))),
                DescribeRole.Definition),
            Node("garg-result", "The prefix antipower exists", "result", Disp(Call("claim")),
                "Binet's identities put the sampled phases in a perturbed half-integer grid. "
                    + "The two parity classes occupy distinct golden cylinder cells. Equality "
                    + "of length-L blocks would imply equality of their length-(F_n−1) prefixes, "
                    + "contradicting the cylinder ranks. The n=3 case has one block; n=6 is "
                    + "checked directly within the proof. The remaining even Fibonacci numbers "
                    + "satisfy the strict residual bounds of the general sample-grid theorem.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("garg-2019-fibonacci-prefix-antipowers"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(formula), provenance,
        declaration == "S" || declaration == "fibW"
            ? Blocks(WordQuotation(), Paragraph(Text(prose)))
            : declaration == "blockLength"
                ? Blocks(SourceQuotation(), Paragraph(Text(prose)))
                : Blocks(Paragraph(Text(prose))), role, resolution);

    private static DocumentBlock WordQuotation() => Paragraph(
        Text("Source definition (§3, printed page 5), verbatim: “We prove that the Fibonacci word "),
        Math(Seq(Mathbf, Grp(F.Id("f")))), Text(", which is equal to "),
        Math(Seq(new Formula.Power(Varphi, Omega), Parenthesized(D(0)))), Text(" for "),
        Math(Seq(Varphi, Parenthesized(D(0)), Eq, D(0, 1))), Text(", "),
        Math(Seq(Varphi, Parenthesized(D(1)), Eq, D(0))),
        Text(" and thus pure morphic but not generated by a uniform morphism, also satisfies Conjecture 3.”"));

    private static DocumentBlock AntipowerQuotation() => Paragraph(
        Text("Source definition (printed page 1), verbatim: “Fici, Restivo, Silva, and Zamboni define a "),
        Math(F.Id("k")), Text("-antipower to be a word composed of "), Math(F.Id("k")),
        Text(" pairwise distinct, concatenated words of equal length.”"));

    private static DocumentBlock SourceQuotation() => Paragraph(
        Text("Conjecture 18 (printed page 8), verbatim: “Let "),
        Math(FibSource(F.Id("n"))), Text(" be an even Fibonacci number. Then, there is an "),
        Math(Parenthesized(Subtract(FibSource(F.Id("n")), D(1)))),
        Text("-antipower with block length "),
        Math(Add(new Formula.Fraction(FibSource(F.Id("n")), D(2)), FibSource(Subtract(F.Id("n"), D(1))))),
        Text(" that is a prefix of "), Math(Seq(Mathbf, Grp(F.Id("f")))), Text(".”"));

    private static Formula DigitFormula()
    {
        var b = F.Id("b");
        return Disp(All("b", Call("Bool"), Equal(Call("digit", b),
            Seq(Operatorname, Grp(F.Id("if")), Sp, b, Sp, Operatorname, Grp(F.Id("then")), Sp,
                D(0), Sp, Operatorname, Grp(F.Id("else")), Sp, D(1)))));
    }

    private static Formula PrefixFormula()
    {
        var n = F.Id("n");
        var zero = Seq(OpenBracket, D(0), CloseBracket);
        var one = Seq(OpenBracket, D(0), Comma, Sp, D(1), CloseBracket);
        var append = Seq(Call("S", Add(n, D(1))), Sp, Plus, Plus, Sp, Call("S", n));
        return Disp(new Formula.Aligned([
            Equal(Call("S", D(0)), zero),
            Equal(Call("S", D(1)), one),
            All("n", Naturals(), Equal(Call("S", Add(n, D(2))), append))]));
    }

    private static Formula WordFormula()
    {
        var i = F.Id("i");
        var indexed = Seq(Parenthesized(Call("S", i)), OpenBracket, i, CloseBracket);
        return Disp(All("i", Naturals(), Equal(Call("fibW", i), indexed)));
    }

    private static Formula LengthFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", Naturals(), Equal(Call("blockLength", n),
            Add(Call(Qualified("Nat", "div"), Fib(n), D(2)), Fib(Subtract(n, D(1)))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n"); var i = F.Id("i"); var j = F.Id("j");
        var bounds = Conjoin(Le(D(1), n), Call("Even", Fib(n)),
            Lt(i, Subtract(Fib(n), D(1))), Lt(j, Subtract(Fib(n), D(1))), NotEqual(i, j));
        var statement = All("n", Naturals(), All("i", Naturals(), All("j", Naturals(),
            Implies(bounds, NotEqual(Block(n, i), Block(n, j))))));
        return Disp(new Formula.Logic(Parenthesized(Call("claim")), FormulaLogicOperator.Iff,
            Parenthesized(statement)));
    }

    private static Formula Block(Formula n, Formula index)
    {
        var t = F.Id("t"); var length = Call("blockLength", n);
        var body = Call("fibW", Add(Multiply(index, length), Call("val", t)));
        return Parenthesized(Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Parenthesized(Seq(t, Sp, Colon, Sp, Call("Fin", length))),
            Sp, Mapsto, Sp, body));
    }

    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Fib(Formula n) => Call(Qualified("Nat", "fib"), n);
    private static Formula FibSource(Formula n) => new Formula.Subscript(F.Id("F"), n);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Call(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Conjoin(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }
}
