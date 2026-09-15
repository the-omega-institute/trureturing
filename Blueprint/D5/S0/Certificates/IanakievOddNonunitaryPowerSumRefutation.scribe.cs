using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class IanakievOddNonunitaryPowerSumRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/IanakievOddNonunitaryPowerSumRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/ianakiev2018a319927");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sequence member 9216 refutes Ianakiev's power-sum divisibility conjecture.",
        H("The OEIS A319927 Odd Non-Unitary Power-Sum Conjecture"),
        Blocks(
            Node("a319927-nonunitary-divisors", "Non-unitary divisors",
                NonunitaryDivisorsFormula(),
                "The divisors d of n are filtered by gcd(d,n/d)>1. The slash denotes "
                    + "natural-number integer division; it is exact because every d in the "
                    + "displayed domain divides n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a319927-all-power-sum", "All non-unitary divisor powers",
                SFormula(),
                "For natural k and n, S(k,n) sums d^k over all non-unitary divisors d of n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a319927-odd-power-sum", "Odd non-unitary divisor powers",
                OFormula(),
                "For natural k and n, O(k,n) restricts the same sum to divisors with "
                    + "remainder one modulo two.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a319927-member", "Membership in A319927",
                MemberFormula(),
                "A positive natural n is a member when O(2,n) is nonzero and divides "
                    + "S(2,n). The nonzero condition follows the PARI isok guard.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a319927-conjecture", "Ianakiev's conjecture",
                ClaimFormula(),
                "For every member n and every natural power k, the conjecture asserts that "
                    + "O(k,n) divides S(k,n).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("a319927-conjecture-refuted", "The conjecture fails at 9216",
                ResultFormula(),
                "At 9216=2^10*3^2 the odd non-unitary divisor set is {3}; O(1,9216)=3 "
                    + "and S(1,9216)=16361, so the claimed divisibility fails. Munn's 2020 "
                    + "question about p=3 and the entry's 2022 remark are not claimed here.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a319927-odd-nonunitary-power-sum-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + DeclarationName(id)),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, claim);

    private static string DeclarationName(string id) => id switch
    {
        "a319927-nonunitary-divisors" => "nonunitaryDivisors",
        "a319927-all-power-sum" => "S",
        "a319927-odd-power-sum" => "O",
        "a319927-member" => "member",
        "a319927-conjecture" => "claim",
        "a319927-conjecture-refuted" => "result",
        _ => throw new ArgumentOutOfRangeException(nameof(id)),
    };

    private static Formula NonunitaryDivisorsFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var exactQuotient = Seq(n, Sp, Slash, Sp, d);
        var predicate = Less(D(1), Call("gcd", d, exactQuotient));
        var filtered = Seq(
            OpenBrace, d, Sp, InMacro, Sp, Call("divisors", n), Sp, Mid, Sp,
            predicate, CloseBrace);
        return Universal(["n"], Equal(Call("nonunitaryDivisors", n), filtered));
    }

    private static Formula SFormula()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var d = F.Id("d");
        return Universal(["k", "n"], Equal(
            Call("S", k, n),
            Sum(d, Call("nonunitaryDivisors", n), new Formula.Power(d, k))));
    }

    private static Formula OFormula()
    {
        var k = F.Id("k");
        var n = F.Id("n");
        var d = F.Id("d");
        var oddDivisors = Seq(
            OpenBrace, d, Sp, InMacro, Sp, Call("nonunitaryDivisors", n), Sp, Mid, Sp,
            Equal(new Formula.Modulo(d, D(2)), D(1)), CloseBrace);
        return Universal(["k", "n"], Equal(
            Call("O", k, n), Sum(d, oddDivisors, new Formula.Power(d, k))));
    }

    private static Formula MemberFormula()
    {
        var n = F.Id("n");
        var membership = And(
            Less(D(0), n),
            Less(D(0), Call("O", D(2), n)),
            Divides(Call("O", D(2), n), Call("S", D(2), n)));
        return Universal(["n"], new Formula.Logic(
            Parenthesized(Call("member", n)), FormulaLogicOperator.Iff,
            Parenthesized(membership)));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var powers = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("k"),
            Naturals(),
            Divides(Call("O", k, n), Call("S", k, n)));
        var members = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            new Formula.Logic(
                Parenthesized(Call("member", n)), FormulaLogicOperator.Implies,
                Parenthesized(powers)));
        return Disp(new Formula.Logic(
            Parenthesized(F.Id("claim")), FormulaLogicOperator.Iff,
            Parenthesized(members)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Universal(string[] names, Formula body) => Disp(
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. names.Select(name => new Formula.BoundVariable(
                FormulaIdentifier.Create(name), Naturals()))],
            body));

    private static Formula Sum(Formula index, Formula domain, Formula summand) => Seq(
        new Formula.Subscript(F.Sum, Seq(index, Sp, InMacro, Sp, domain)),
        Sp, Parenthesized(summand));

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
