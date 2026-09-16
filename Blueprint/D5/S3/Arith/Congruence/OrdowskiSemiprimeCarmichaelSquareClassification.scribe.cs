using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class OrdowskiSemiprimeCarmichaelSquareClassificationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/OrdowskiSemiprimeCarmichaelSquareClassification.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/ordowski2020a306270");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordowski's semiprimes in A306270 have the prime factors prescribed by A190275.",
        H("Ordowski's A306270 Semiprime Classification"),
        Blocks(
            Paragraph(Text(
                "All variables range over the natural numbers N, including zero. The letter k "
                    + "denotes a sequence candidate, p and q denote prime factors with p at most "
                    + "q, and b denotes an arbitrary residue representative. Prime(x) means that "
                    + "x is prime, gcd is the natural greatest common divisor, mem is membership "
                    + "in A306270, and congruence is taken modulo the displayed natural modulus. "
                    + "Powers, products, order, and subtraction are natural-number operations, so "
                    + "subtraction is truncated at zero. The scope is exactly Ordowski's Conjecture "
                    + "sentence for every semiprime k greater than four. The classification proof "
                    + "is content-bearing: it turns the universal congruence into a Carmichael "
                    + "exponent divisibility and follows the prime-square divisor chain to the "
                    + "factor equality.")),
            Node(
                "mem",
                "Membership in A306270",
                MembershipFormula(),
                "A natural number k belongs to A306270 when it is composite and greater than one, "
                    + "and every natural b coprime to k has b^(k(k-1)) congruent to one modulo k^2.",
                DescribeRole.Definition),
            Node(
                "result",
                "Ordowski's semiprime classification",
                ResultFormula(),
                "If k=pq is greater than four, p and q are prime, p is at most q, and k belongs "
                    + "to A306270, then q=p^2-p+1. Consequently k has the form p(p^2-p+1) from "
                    + "A190275. The subtraction in the displayed equality is natural subtraction.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a306270-ordowski-semiprime-carmichael-square-classification"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a306270-" + name),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula MembershipFormula()
    {
        var k = F.Id("k");
        var b = F.Id("b");
        var exponent = Multiply(k, Subtract(k, D(1)));
        var modulus = Power(k, D(2));
        var universalCongruence = Universal(["b"], Implies(
            Equal(Call("gcd", b, k), D(1)),
            Congruent(Power(b, exponent), D(1), modulus)));
        var membership = And(
            new Formula.Not(Call("Prime", k)),
            Less(D(1), k),
            universalCongruence);
        return Disp(Universal(["k"], Iff(Call("mem", k), membership)));
    }

    private static Formula ResultFormula()
    {
        var p = F.Id("p");
        var q = F.Id("q");
        var product = Multiply(p, q);
        var conclusion = Equal(
            q,
            Add(Subtract(Power(p, D(2)), p), D(1)));
        var statement = Implies(
            Call("Prime", p),
            Implies(
                Call("Prime", q),
                Implies(
                    LessOrEqual(p, q),
                    Implies(
                        Less(D(4), product),
                        Implies(Call("mem", product), conclusion)))));
        return Disp(Universal(["p", "q"], statement));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Universal(string[] variables, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. variables.Select(variable =>
                new Formula.BoundVariable(FormulaIdentifier.Create(variable), Naturals()))],
            body);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula Congruent(Formula left, Formula right, Formula modulus) =>
        Seq(left, Sp, Equiv, Sp, right, Sp,
            Parenthesized(Seq(Named("mod"), Sp, modulus)));
}
