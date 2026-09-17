using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class ErdosConsecutiveProductSquarefreeFactorRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/ErdosConsecutiveProductSquarefreeFactorRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/erdos1985consecutive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The starting value 47 refutes the proposed uniqueness of 23 among starting "
            + "values whose consecutive products always have dominant repeated factors.",
        H("Erdos's Consecutive-Product Factor Question"),
        Blocks(
            Node("consecutive-product", "The consecutive product", "P", PFormula(),
                "P(x,k) is the product of the k consecutive integers immediately after x.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("single-exponent-factor", "The single-exponent factor", "v", VFormula(),
                "The factor v(x,k) is the product of exactly those primes whose exponent "
                    + "in P(x,k) equals one. It is not the squarefree part of P(x,k).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("repeated-prime-power-factor", "The repeated-prime-power factor", "u",
                UFormula(),
                "The factor u(x,k) contains each prime power whose exponent in P(x,k) is "
                    + "at least two, with that full exponent.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("unique-counterexample-claim", "The proposed uniqueness of 23", "claim",
                ClaimFormula(),
                "Every positive starting value other than 23 is asserted to admit a positive "
                    + "length for which the single-exponent factor exceeds the repeated factor.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("unique-counterexample-refuted", "The starting value 47 is another exception",
                "result", ResultFormula(),
                "For x=47, direct factor-exponent arguments handle lengths 1 through 78. "
                    + "For every length at least 79, an inductive exponential lower bound "
                    + "for P combines with the primorial upper bound for v to give v<u. "
                    + "This leaves conjecture (22) and the statement about x=23 untouched.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "erdos-1985-consecutive-product-squarefree-factor-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))),
        role, resolution);

    private static Formula PFormula()
    {
        Formula x = F.Id("x"), k = F.Id("k"), i = F.Id("i");
        Formula range = Call("Icc", D(1), k);
        Formula product = Seq(
            new Formula.Subscript(Prod, Seq(i, Sp, InMacro, Sp, range)),
            Sp, Parenthesized(Add(x, i)));
        return Disp(ForAllNaturals(x, k, Equal(Call("P", x, k), product)));
    }

    private static Formula VFormula()
    {
        Formula x = F.Id("x"), k = F.Id("k"), p = F.Id("p");
        Formula product = Call("P", x, k);
        Formula exponent = FactorizationAt(product, p);
        Formula filtered = FilteredPrimes(p, product, Equal(exponent, D(1)));
        Formula value = Seq(
            new Formula.Subscript(Prod, Seq(p, Sp, InMacro, Sp, filtered)), Sp, p);
        return Disp(ForAllNaturals(x, k, Equal(Call("v", x, k), value)));
    }

    private static Formula UFormula()
    {
        Formula x = F.Id("x"), k = F.Id("k"), p = F.Id("p");
        Formula product = Call("P", x, k);
        Formula exponent = FactorizationAt(product, p);
        Formula filtered = FilteredPrimes(p, product, AtMost(D(2), exponent));
        Formula value = Seq(
            new Formula.Subscript(Prod, Seq(p, Sp, InMacro, Sp, filtered)), Sp,
            new Formula.Power(p, exponent));
        return Disp(ForAllNaturals(x, k, Equal(Call("u", x, k), value)));
    }

    private static Formula ClaimFormula()
    {
        Formula x = F.Id("x"), k = F.Id("k");
        Formula witness = new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create("k"), Naturals(),
            And(AtMost(D(1), k), Less(Call("u", x, k), Call("v", x, k))));
        Formula quantified = new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("x"), Naturals(),
            Implies(
                AtMost(D(1), x),
                NotEqual(x, D(2, 3)),
                witness));
        return Disp(IffFormula(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula FilteredPrimes(
        Formula p, Formula product, Formula condition) => Seq(
            OpenBrace, p, Sp, InMacro, Sp, Call("primeFactors", product), Sp, Mid, Sp,
            condition, CloseBrace);

    private static Formula FactorizationAt(Formula value, Formula p) =>
        new Formula.Apply(Call("factorization", value), [p]);

    private static Formula ForAllNaturals(Formula first, Formula second, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(Identifier(first), Naturals()),
                new Formula.BoundVariable(Identifier(second), Naturals()),
            ],
            body);

    private static FormulaIdentifier Identifier(Formula value) => value switch
    {
        Formula.LatexWord word => word.Value,
        _ => throw new ArgumentOutOfRangeException(nameof(value)),
    };

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.And, result);
        }

        return result;
    }

    private static Formula Implies(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = new Formula.Logic(
                Parenthesized(clauses[index]), FormulaLogicOperator.Implies, result);
        }

        return result;
    }

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff,
            Parenthesized(right));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
