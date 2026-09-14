using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class DetlefsFibonacciFermatPrimeCharacterizationRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/DetlefsFibonacciFermatPrimeCharacterizationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/sloane2014a000040");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The composite 219781 refutes Detlefs's Fibonacci-Fermat prime characterization.",
        H("The OEIS A000040 Fibonacci-Fermat Prime Characterization"),
        Blocks(
            Node("fibonacci-test", "The Fibonacci residue test", FibTestFormula(),
                "For each natural n, fibTest(n) holds when the Fibonacci number F(n) "
                    + "has remainder one or n minus one modulo n.",
                "fibTest", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("fermat-test", "The Fermat residue test", FermatTestFormula(),
                "For each natural n, fermatTest(n) holds when two to the power n minus "
                    + "one has remainder one modulo n.",
                "fermatTest", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("detlefs-set", "Detlefs's proposed set", InDetlefsSetFormula(),
                "The proposed set contains five, together with every natural n distinct "
                    + "from five that satisfies both residue tests.",
                "inDetlefsSet", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("prime-characterization", "Detlefs's prime characterization", ClaimFormula(),
                "For every positive natural n, the characterization identifies primality "
                    + "exactly with membership in the proposed set.",
                "claim", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("prime-characterization-refuted", "The characterization fails at 219781",
                ResultFormula(),
                "The value 219781 equals 271 times 811 and is composite, while its Fibonacci "
                    + "remainder and its two-to-the-219780 remainder modulo 219781 are both one. "
                    + "Thus it belongs to the proposed set and refutes the characterization. "
                    + "At the degenerate boundary, the prime two is also outside the proposed "
                    + "set because two to the first power has remainder zero modulo two. The "
                    + "Fibonacci-type pseudoprime status of 219781 is prior art recorded by "
                    + "OEIS A094401, A093372, and A212424.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a000040-detlefs-fibonacci-fermat-prime-characterization-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        string declaration,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula FibTestFormula()
    {
        var n = F.Id("n");
        var fibonacciResidue = new Formula.Modulo(Call("Fibonacci", n), n);
        return Disp(Universal("n", Iff(
            Call("fibTest", n),
            Or(
                Equal(fibonacciResidue, D(1)),
                Equal(fibonacciResidue, Subtract(n, D(1)))))));
    }

    private static Formula FermatTestFormula()
    {
        var n = F.Id("n");
        var exponent = Subtract(n, D(1));
        return Disp(Universal("n", Iff(
            Call("fermatTest", n),
            Equal(new Formula.Modulo(new Formula.Power(D(2), exponent), n), D(1)))));
    }

    private static Formula InDetlefsSetFormula()
    {
        var n = F.Id("n");
        return Disp(Universal("n", Iff(
            Call("inDetlefsSet", n),
            Or(
                Equal(n, D(5)),
                And(
                    NotEqual(n, D(5)),
                    Call("fibTest", n),
                    Call("fermatTest", n))))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var characterization = Iff(
            Call("Prime", n),
            Call("inDetlefsSet", n));
        var quantified = Universal("n", Implies(
            Less(D(0), n), characterization));
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable),
            Naturals(),
            body);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Or(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.Or, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
