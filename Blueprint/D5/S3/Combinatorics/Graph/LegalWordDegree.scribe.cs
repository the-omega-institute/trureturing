using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class LegalWordDegreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LegalWordDegree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Legal binary words have one neighbour per occupied position or flippable zero. "
        + "The flippable-zero count plus twice the occupation count is at most n+1, "
        + "with equality exactly for odd alternating words beginning and ending in one.",
        H("Degrees and the sharp count bound for legal words"),
        Blocks(
            Paragraph(Text(
                "A legal word is a Boolean function on Fin n satisfying Adm: adjacent positions "
                + "cannot both be true. Positions are indexed from zero. The graph is the induced "
                + "subgraph of the Boolean hypercube, so its edges have actual Hamming distance one. "
                + "The occupation count is the existing sum of the Boolean values converted to naturals.")),
            Describe.Lean(DescribeId.Create("legal-word-graph"),
                DeclarationHandle.Create(Prefix + "legalWordGraph"), H("The induced legal-word graph"),
                StatementSource.FromAuthor(GraphFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Vertices are the literal subtype of admissible Boolean words. Adjacency is "
                    + "inherited from the hypercube."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("flippable-zero"),
                DeclarationHandle.Create(Prefix + "FlippableZero"), H("A flippable zero position"),
                StatementSource.FromAuthor(FlippableFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The position itself is false, and every existing immediate neighbour is false. "
                    + "A missing left or right neighbour is taken to be zero. Thus the two endpoint "
                    + "conditions are exactly the same as padding the word with a zero on each side."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("flippable-zero-count"),
                DeclarationHandle.Create(Prefix + "flippableZeroCount"), H("Counting flippable zeros"),
                StatementSource.FromAuthor(CountFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The count sums one for each flippable zero and zero for every other position."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("degree-count"),
                DeclarationHandle.Create(Prefix + "degree_eq_flippable_add_occupation"),
                H("Degree equals additions plus removals"),
                StatementSource.FromAuthor(DegreeFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Removing a one always preserves legality. Adding a one preserves legality "
                    + "exactly at a flippable zero. These legal flips give a bijection from the "
                    + "eligible positions to the actual neighbour set. A neighbour differs at exactly "
                    + "one position, so this accounts for every edge without duplication."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sharp-count-bound"),
                DeclarationHandle.Create(Prefix + "flippable_bound_and_equality"),
                H("The sharp bound and its complete equality condition"),
                StatementSource.FromAuthor(BoundFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every length and every legal word, u+2k is at most n+1. Equality holds "
                    + "exactly when n is odd and position i is true exactly when i is even. "
                    + "The proof separates a leading zero from a leading one followed by zero. "
                    + "Removing a leading zero preserves the tail's flippable positions and removes "
                    + "at most one extra flippable zero; equality is impossible in this branch. "
                    + "Removing a leading 10 preserves u and decreases k by one, reducing both "
                    + "the bound and the equality condition to the shorter word. The length-one "
                    + "word 1 attains equality. The empty word satisfies the strict inequality, "
                    + "and all-zero words, even lengths, and zero endpoints are included."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(name))
        : new Formula.Apply(new Formula.NamedConstant(FormulaIdentifier.Create(name)), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Nat() => Call("Nat");
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Word(Formula n) => new Formula.TypeArrow(Fin(n), Call("Bool"));
    private static Formula Legal(Formula n) => Seq(OpenBrace, F.Id("w"), Colon, Sp, Word(n),
        Sp, Mid, Sp, Call("Adm", n, F.Id("w")), CloseBrace);
    private static Formula Val(Formula b) => Call("val", b);
    private static Formula U(Formula b) => Call("flippableZeroCount", b);
    private static Formula K(Formula b) => Call("occupationCount", b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id(name), Colon, Sp, type)), Sp, Parenthesized(body));

    private static Formula GraphFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), c = F.Id("c");
        return Disp(All("n", Nat(), All("b", Legal(n), All("c", Legal(n),
            Iff(Call("Adj", Call("legalWordGraph", n), b, c),
                Eq(Call("hammingDist", Val(b), Val(c)), D(1)))))));
    }

    private static Formula FlippableFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w"), i = F.Id("i"), j = F.Id("j");
        Formula adjacent = Or(Eq(Add(Val(j), D(1)), Val(i)), Eq(Add(Val(i), D(1)), Val(j)));
        return Disp(All("n", Nat(), All("w", Word(n), All("i", Fin(n),
            Iff(Call("FlippableZero", w, i), And(Eq(App(w, i), Call("false")),
                All("j", Fin(n), Imp(adjacent, Eq(App(w, j), Call("false"))))))))));
    }

    private static Formula CountFormula()
    {
        Formula n = F.Id("n"), w = F.Id("w");
        return Disp(All("n", Nat(), All("w", Word(n), Eq(U(w),
            SumOver("i", Fin(n), Call("ite", Call("FlippableZero", w, F.Id("i")), D(1), D(0)))))));
    }

    private static Formula DegreeFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b");
        return Disp(All("n", Nat(), All("b", Legal(n),
            Eq(Call("degree", Call("legalWordGraph", n), b), Add(U(Val(b)), K(Val(b)))))));
    }

    private static Formula BoundFormula()
    {
        Formula n = F.Id("n"), b = F.Id("b"), i = F.Id("i");
        Formula count = Add(U(Val(b)), Mul(D(2), K(Val(b))));
        Formula bound = new Formula.Relation(count, FormulaRelationOperator.LessThanOrEqual, Add(n, D(1)));
        Formula alternating = All("i", Fin(n), Eq(App(Val(b), i),
            Call("decide", Eq(new Formula.Modulo(Val(i), D(2)), D(0)))));
        return Disp(All("n", Nat(), All("b", Legal(n), And(bound,
            Iff(Eq(count, Add(n, D(1))), And(Call("Odd", n), alternating))))));
    }
}
