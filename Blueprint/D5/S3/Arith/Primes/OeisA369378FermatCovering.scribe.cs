using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class OeisA369378FermatCoveringDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Primes/OeisA369378FermatCovering.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/ordowski2024a369378");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordowski's A369378 conjecture is proved by a Fermat-number covering.",
        H("Ordowski A369378: the Fermat-number covering proof"),
        Blocks(
            Paragraph(Text(
                "The variables n and k are natural numbers. The source sentence is quoted "
                    + "verbatim in the claim description: \"Conjecture: if n > 0, then "
                    + "2^(2^n+1)-1 + 2^k is not prime for every k < 2^n.\" The Lean encoding "
                    + "uses 0 < n, the natural bound k < 2^n including k = 0, natural subtraction, "
                    + "and Nat.Prime. The proof selects F_j = 2^(2^j)+1 from the odd part of k; "
                    + "modulo F_j, the large power is 2 and 2^k is -1.")),
            Node("claim", "Ordowski's conjecture", ClaimDefinition(),
                "OEIS A369378, COMMENTS (unpaginated): \"Conjecture: if n > 0, then "
                    + "2^(2^n+1)-1 + 2^k is not prime for every k < 2^n.\" The formula "
                    + "below preserves the natural-number expression and its quantifiers exactly.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The Fermat-number covering settlement", ClaimBody(),
                "For k = 0, the number is a power of two with a proper divisor. For positive k, "
                    + "write k as 2^j times an odd number; k < 2^n gives j < n. The Fermat number "
                    + "2^(2^j)+1 divides the target by the congruences 2^(2^n) = 1 and 2^k = -1 "
                    + "in its residue ring, and it is a proper divisor. The finite fidelity examples "
                    + "at n = 1 and n = 2 certify the boundary primes 11 and 47.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("a369378-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string name) => F.Id(name);
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Named(owner), Dot, Named(name));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat(), body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula Prime(Formula value) =>
        new Formula.Apply(Qualified("Nat", "Prime"), [value]);

    private static Formula Target(Formula n, Formula k) =>
        Add(Subtract(Power(D(2), Add(Power(D(2), n), D(1))), D(1)), Power(D(2), k));

    private static Formula ClaimBody()
    {
        Formula n = V("n");
        Formula k = V("k");
        Formula hypotheses = Implication(Less(D(0), n),
            Implication(Less(k, Power(D(2), n)),
                new Formula.Not(Parenthesized(Prime(Target(n, k))))));
        return All("n", All("k", hypotheses));
    }

    private static Formula ClaimDefinition() =>
        Equal(Call("claim"), Parenthesized(ClaimBody()));
}
