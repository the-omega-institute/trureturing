using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SchulteOmegaBinomialConvolutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/SchulteOmegaBinomialConvolution.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/schulte2018a001222");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's binomial convolution relates the total and distinct prime-factor counts.",
        H("Schulte's Omega Binomial Convolution"),
        Blocks(
            Paragraph(Text("C denotes the complex numbers and N the natural numbers including "
                + "zero. Omega, written Ω, is A001222, the number of prime factors counted "
                + "with multiplicity; omega, written ω, is A001221, the number of distinct "
                + "prime factors. Their difference is A046660. Subtraction in the exponent "
                + "is natural-number subtraction; omega(n) is at most Omega(n), so no "
                + "truncation changes this difference. The sum ranges over all positive "
                + "divisors d of n, including one and n. The slash n/d denotes natural-number "
                + "division, which is exact on this divisor set. Powers have natural "
                + "exponents, including the convention 0^0 = 1. Only Schulte's general "
                + "x, y conjecture for positive n is asserted here. The case x = 1 - y "
                + "is the Dressler-van de Lune 1973 result; other OEIS assertions are "
                + "outside the claim.")),
            Describe.Lean(DescribeId.Create("a001222-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The binomial divisor convolution"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Both sides define multiplicative arithmetic functions "
                    + "after setting their values at zero to zero. On each prime power the "
                    + "convolution becomes a finite geometric sum. Its polynomial identity "
                    + "holds even when y or x+y is zero. Equality on prime powers then "
                    + "gives the identity at every positive natural index."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a001222-schulte-omega-binomial-convolution"),
                    ResolutionKind.Proved)))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, Formula argument) =>
        new Formula.Apply(Named(name), [argument]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Bound(Formula variable, Formula domain) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula ResultFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), n = F.Id("n"), d = F.Id("d");
        Formula sumBase = Parenthesized(new Formula.Binary(x, FormulaBinaryOperator.Add, y));
        Formula quotient = Seq(n, Sp, Slash, Sp, d);
        Formula exponent = new Formula.Binary(Call("Omega", quotient),
            FormulaBinaryOperator.Subtract, Call("omega", quotient));
        Formula summand = Multiply(new Formula.Power(x, Call("Omega", d)),
            Parenthesized(Multiply(new Formula.Power(sumBase, exponent),
                new Formula.Power(y, Call("omega", quotient)))));
        Formula divisorSum = Seq(new Formula.Subscript(F.Sum,
            new Formula.Relation(d, FormulaRelationOperator.Divides, n)), Sp, summand);
        Formula conclusion = new Formula.Relation(new Formula.Power(sumBase, Call("Omega", n)),
            FormulaRelationOperator.Equal, divisorSum);
        return Disp(Seq(Bound(x, Complexes()), Bound(y, Complexes()), Bound(n, Naturals()),
            Parenthesized(new Formula.Relation(D(0), FormulaRelationOperator.LessThan, n)),
            Sp, Implies, Sp, Parenthesized(conclusion)));
    }
}
