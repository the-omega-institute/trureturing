using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class CaceresGcdFactorialPowerPrimeCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/CaceresGcdFactorialPowerPrimeCriterion.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/caceres2019a308090");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Caceres' A308090 gcd-factorial-power condition implies primality.",
        H("Caceres' A308090 gcd-factorial-power primality criterion"),
        Blocks(
            Paragraph(Text(
                "All variables range over the natural numbers N, including zero. "
                    + "The index is n; a(n) is the A308090 value; exponentiation, "
                    + "addition, and factorial are natural-number operations; gcd is "
                    + "the natural greatest common divisor; and Prime(x) means that x "
                    + "is prime. The constants 0, 1, 2, and 3 are natural numbers, n+1 "
                    + "is the successor of n, 0<n means that n is positive, equality is "
                    + "natural equality, and each arrow is logical implication. The "
                    + "scope is exactly the unsigned OEIS Conjecture "
                    + "sentence for every positive n. The case n=0 is excluded because "
                    + "its hypothesis holds while 1 is not prime. The proof takes a prime "
                    + "divisor q of a composite n+1, observes q<=n so that q divides n!, "
                    + "hence q divides both 2^n and 3^n, hence both 2 and 3, a contradiction.")),
            Node(
                "a",
                "The A308090 sequence",
                DefinitionFormula(),
                "The sequence value is the gcd of the two factorial-shifted powers "
                    + "and the successor n+1.",
                DescribeRole.Definition),
            Node(
                "result",
                "Caceres' primality criterion",
                ResultFormula(),
                "For every positive natural index, equality of a(n) with n+1 implies "
                    + "that n+1 is prime. A prime divisor of a hypothetical composite "
                    + "successor divides n factorial and both shifted powers, hence "
                    + "divides both 2 and 3, which is impossible.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a308090-caceres-gcd-factorial-power-prime-criterion"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a308090-" + name),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        AssessedProvenance.FromLiterature(Source),
        Blocks(Paragraph(Text(prose))),
        role,
        claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula Successor(Formula n) => Add(n, D(1));

    private static Formula ShiftedPower(Formula @base, Formula n) =>
        Add(Power(@base, n), Call("factorial", n));

    private static Formula DefinitionFormula()
    {
        var nIdentifier = FormulaIdentifier.Create("n");
        var n = new Formula.LatexWord(nIdentifier);
        var value = Call(
            "gcd",
            Call("gcd", ShiftedPower(D(2), n), ShiftedPower(D(3), n)),
            Successor(n));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            nIdentifier,
            Naturals(),
            Equal(Call("a", n), value)));
    }

    private static Formula ResultFormula()
    {
        var nIdentifier = FormulaIdentifier.Create("n");
        var n = new Formula.LatexWord(nIdentifier);
        var equality = Equal(Call("a", n), Successor(n));
        var primality = Call("Prime", Successor(n));
        var criterion = new Formula.Logic(
            Parenthesized(equality),
            FormulaLogicOperator.Implies,
            Parenthesized(primality));
        var implication = new Formula.Logic(
            Parenthesized(Less(D(0), n)),
            FormulaLogicOperator.Implies,
            Parenthesized(criterion));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            nIdentifier,
            Naturals(),
            implication));
    }
}
