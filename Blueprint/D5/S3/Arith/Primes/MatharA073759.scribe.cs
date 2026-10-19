using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class MatharA073759Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/MatharA073759.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/mathar2026a073759");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mathar's A073759 conjecture holds for every natural index at least five.",
        H("The largest number neither dividing nor coprime to n"),
        Blocks(
            Node("a", "OEIS A073759", SequenceFormula(),
                "OEIS A073759, NAME (unpaginated): \"Largest number < n that is neither a divisor of nor relatively prime to n, or 0 if no such number exists.\" "
                + "The candidates are the positive natural numbers m in Finset.Ico 1 n. "
                + "Finset.filter keeps exactly those with neither m dividing n nor Nat.Coprime m n. "
                + "Finset.sup id selects the largest candidate and is zero for the empty set. The entry has offset 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A046666", "Subtracting the least prime factor", FactorFormula(),
                "OEIS A046666, FORMULA (unpaginated): \"a(n) = n - (smallest prime dividing n).\" "
                + "Nat.minFac is the least prime factor at every n at least two, the entry's offset. "
                + "Subtraction is truncated natural subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A046667", "Half the difference", HalfFormula(),
                "OEIS A046667, FORMULA (unpaginated): \"a(n) = A046666(n)/2.\" "
                + "Nat.div is natural integer division, rounding down; the entry has offset 2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Mathar's conjecture", Disp(Equal(F.Id("claim"), Parenthesized(ClaimBody()))),
                "OEIS A073759, FORMULA (unpaginated): \"Conjecture: a(n) = 2*A046667(n) if n>=5. - _R. J. Mathar_, May 15 2026\". "
                + "The quantifier ranges over all natural n at least five; a is A073759 and A046667 is defined above.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The conjecture holds", Disp(ClaimBody()),
                "For prime n every positive k below n is coprime to n, so a(n) is zero. "
                + "For composite n at least five, set p = Nat.minFac n. The inequality p squared at most n "
                + "gives 2p < n. Thus n-p has gcd p with n, strictly smaller than n-p, "
                + "and is neither a divisor of n nor coprime to n. A common prime divisor r of any k < n "
                + "and n divides n-k, so p is at most r and r is at most n-k. This bounds every candidate by n-p. "
                + "Finally n-p is even: an even n has p=2, and an odd n has odd p. "
                + "Hence a(n)=n-p=2*A046667(n).",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mathar-oeis-a073759-least-prime-factor"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("mathar-a073759-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula All(string name, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat, body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var predicate = new Formula.Logic(
            Parenthesized(new Formula.Not(Parenthesized(new Formula.Relation(m, FormulaRelationOperator.Divides, n)))),
            FormulaLogicOperator.And,
            Parenthesized(new Formula.Not(Apply(Qualified("Nat", "Coprime"), m, n))));
        var lambda = Parenthesized(Seq(Operatorname, Grp(F.Id("fun")), Sp, m, Sp, Colon, Sp, Nat,
            Sp, Mapsto, Sp, predicate));
        var interval = Apply(Qualified("Finset", "Ico"), D(1), n);
        var candidates = Apply(Qualified("Finset", "filter"), lambda, interval);
        return Disp(All("n", Equal(Call("a", n),
            Apply(Qualified("Finset", "sup"), candidates, F.Id("id")))));
    }

    private static Formula FactorFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", Equal(Call("A046666", n),
            Subtract(n, Apply(Qualified("Nat", "minFac"), n)))));
    }

    private static Formula HalfFormula()
    {
        var n = F.Id("n");
        return Disp(All("n", Equal(Call("A046667", n),
            Apply(Qualified("Nat", "div"), Call("A046666", n), D(2)))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        return All("n", new Formula.Logic(
            Parenthesized(new Formula.Relation(D(5), FormulaRelationOperator.LessThanOrEqual, n)),
            FormulaLogicOperator.Implies,
            Parenthesized(Equal(Call("a", n), Multiply(D(2), Call("A046667", n))))));
    }
}
