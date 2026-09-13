using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class DivisorCountPrimeFactorBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/DivisorCountPrimeFactorBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/wiseman2019a328959");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The divisor-count expression in OEIS A328959 is nonnegative from n=2 onward.",
        H("The A328959 Divisor-Count Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a328959-sequence"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The integer-valued sequence"),
                StatementSource.FromAuthor(SequenceFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The formula is a(n) = sigma_0(n) - 2 - (Omega(n) - 1) times omega(n). "
                    + "Here sigma_0 is the number of divisors (A000005), Omega is the number "
                    + "of prime factors with multiplicity (the entry's omega, A001222), and "
                    + "omega is the number of distinct prime factors (the entry's nu, A001221). "
                    + "The values are integers. The source's exceptional value is a(1)=-1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a328959-nonnegative"),
                DeclarationHandle.Create(Prefix + "wiseman_a328959"),
                H("Nonnegativity from two onward"),
                StatementSource.FromAuthor(NonnegativeFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n at least two, write each positive prime exponent as one plus b. "
                    + "The product of the factors two plus b dominates its constant and "
                    + "linear parts. Two inductive power estimates then bound the distinct "
                    + "prime count and its quadratic term, proving that a(n) is nonnegative."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a328959-divisor-count-prime-factor-bound"),
                    ResolutionKind.Proved)))));

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n");
        Formula product = new Formula.Binary(
            new Formula.Binary(Call("cardFactors", n), FormulaBinaryOperator.Subtract, D(1)),
            FormulaBinaryOperator.Multiply,
            Call("cardDistinctFactors", n));
        Formula value = new Formula.Binary(
            new Formula.Binary(Call("sigmaZero", n), FormulaBinaryOperator.Subtract, D(2)),
            FormulaBinaryOperator.Subtract,
            Parenthesized(product));
        return Disp(BindNatural(n,
            new Formula.Relation(Call("a", n), FormulaRelationOperator.Equal, value)));
    }

    private static Formula NonnegativeFormula()
    {
        Formula n = F.Id("n");
        Formula lowerBound = new Formula.Relation(D(2), FormulaRelationOperator.LessThanOrEqual, n);
        Formula nonnegative = new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, Call("a", n));
        return Disp(BindNatural(n,
            new Formula.Logic(lowerBound, FormulaLogicOperator.Implies, nonnegative)));
    }

    private static Formula BindNatural(Formula variable, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create("n"), Naturals())],
        body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
