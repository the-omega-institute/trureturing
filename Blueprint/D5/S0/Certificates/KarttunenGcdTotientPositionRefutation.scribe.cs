using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class KarttunenGcdTotientPositionRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/KarttunenGcdTotientPositionRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/karttunen2007a129598");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The value 60 refutes Karttunen's A089966 characterization of A129598 differences.",
        H("The OEIS A129598 Differing-Position Conjecture"),
        Blocks(
            Node("gcd-totient-map", "The gcd-totient map", GFormula(),
                "For each natural m, g(m) is the greatest common divisor of m and Euler's "
                    + "totient of m.",
                "g", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("greatest-prime-factor", "The greatest-prime-factor function",
                GreatestPrimeFactorFormula(),
                "The prime factors are listed with multiplicity in increasing order. The last "
                    + "entry is the greatest prime factor, with default zero when the list is empty.",
                "greatestPrimeFactor", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("a129598-sequence", "The A129598 sequence", AFormula(),
                "The initial value is a(1)=2. At every other natural n, a(n) is n times its "
                    + "greatest prime factor.",
                "a", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a050399-sequence", "The A050399 sequence", BFormula(),
                "When a positive preimage of n under g exists, b(n) is the least such natural "
                    + "number; Nat.find supplies that least element. If the existence condition "
                    + "fails, the definition returns zero.",
                "b", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a089966-membership", "Membership in A089966", InA089966Formula(),
                "Membership holds at one, or at a positive n when the number of distinct prime "
                    + "factors equals the greatest prime factor modulo the least prime factor.",
                "inA089966", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("differing-position-claim", "Karttunen's differing-position characterization",
                ClaimFormula(),
                "For every natural n greater than one, the characterization identifies a(n) "
                    + "and b(n) as unequal exactly at the members of A089966.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("differing-position-refuted", "The characterization fails at 60",
                ResultFormula(),
                "At n=60, a(60)=300 has gcd-totient value 20 rather than 60, while b(60) "
                    + "has gcd-totient value 60 because 900 supplies a positive preimage. Thus "
                    + "a(60) and b(60) differ, but 60 is not in A089966. This refutes only the "
                    + "differing-position characterization; Conjecture 2 is untouched.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a129598-gcd-totient-position-refutation"),
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

    private static Formula GFormula()
    {
        var m = F.Id("m");
        return Disp(Universal("m", Equal(
            Call("g", m), Call("gcd", m, Call("totient", m)))));
    }

    private static Formula GreatestPrimeFactorFormula()
    {
        var n = F.Id("n");
        return Disp(Universal("n", Equal(
            Call("greatestPrimeFactor", n),
            Call("getLastD", Call("primeFactorsList", n), D(0)))));
    }

    private static Formula AFormula()
    {
        var n = F.Id("n");
        return Disp(Universal("n", Equal(
            Call("a", n),
            Call("if", Equal(n, D(1)), D(2),
                Multiply(n, Call("greatestPrimeFactor", n))))));
    }

    private static Formula BFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var condition = And(
            Less(D(0), m),
            Equal(Call("g", m), n));
        var existence = ExistsOverNaturals("m", condition);
        var candidates = Seq(
            OpenBrace, m, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            Parenthesized(condition), CloseBrace);
        return Disp(Universal("n", Equal(
            Call("b", n),
            Call("if", existence, Call("sInf", candidates), D(0)))));
    }

    private static Formula InA089966Formula()
    {
        var n = F.Id("n");
        var arithmeticClause = And(
            Less(D(0), n),
            Equal(
                Call("card", Call("primeFactors", n)),
                new Formula.Modulo(
                    Call("greatestPrimeFactor", n), Call("minFac", n))));
        return Disp(Universal("n", Iff(
            Call("inA089966", n),
            Or(Equal(n, D(1)), arithmeticClause))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var characterization = Iff(
            NotEqual(Call("a", n), Call("b", n)),
            Call("inA089966", n));
        var quantified = Universal("n", Implies(
            Less(D(1), n), characterization));
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

    private static Formula ExistsOverNaturals(string variable, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
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

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));

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

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
