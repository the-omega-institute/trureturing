using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class KrizekDivisorSigmaModNoncompositeDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithSums/KrizekDivisorSigmaModNoncomposite.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithSums/krizek2018a300657");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Krizek's divisor sum of sigma residues equals the final residue exactly at one and the primes.",
        H("Krizek's A300657 noncomposite characterization"),
        Blocks(
            Paragraph(Text(
                "All variables and values are natural numbers. The notation sigma(1,d) "
                    + "denotes the sum of the positive divisors of d, and b mod d denotes "
                    + "the natural-number remainder of b upon division by d.")),
            Node(
                "a300657",
                "The divisor sigma-residue sum",
                DefinitionFormula(),
                "For each n, the sum ranges over the positive divisors d of n and adds "
                    + "the remainder of sigma(1,d) modulo d. At zero the divisor set is "
                    + "empty; the characterization below starts at one.",
                DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node(
                "result",
                "The noncomposite characterization",
                ResultFormula(),
                "The entry states: \"a(n) >= A054024(n). Conjecture: a(n) = "
                    + "A054024(n) only for the noncomposite numbers A008578.\" For every "
                    + "n at least one, the divisor residue sum equals the final sigma "
                    + "residue exactly when n is one or prime. For a composite n, "
                    + "its least prime factor is a proper divisor and contributes one "
                    + "modulo itself, so the remaining nonnegative divisor terms cannot "
                    + "sum to zero. At one and at a prime, the divisor set evaluates "
                    + "directly.",
                DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(
        string name,
        string title,
        Formula formula,
        string prose,
        DescribeRole role,
        AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("a300657-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name),
        H(title),
        StatementSource.FromAuthor(formula),
        provenance,
        Blocks(Paragraph(Text(prose))),
        role);

    private static Formula DefinitionFormula()
    {
        var n = F.Id("n");
        var d = F.Id("d");
        var divisorSum = DivisorSum(
            d,
            n,
            new Formula.Modulo(Call("sigma", D(1), d), d));
        return Universal(Equal(Call("a300657", n), divisorSum));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var equality = Equal(
            Call("a300657", n),
            new Formula.Modulo(Call("sigma", D(1), n), n));
        var noncomposite = new Formula.Logic(
            Parenthesized(Equal(n, D(1))),
            FormulaLogicOperator.Or,
            Parenthesized(Call("Prime", n)));
        var criterion = new Formula.Logic(
            Parenthesized(equality),
            FormulaLogicOperator.Iff,
            Parenthesized(noncomposite));
        return Universal(new Formula.Logic(
            Parenthesized(LessOrEqual(D(1), n)),
            FormulaLogicOperator.Implies,
            Parenthesized(criterion)));
    }

    private static Formula Universal(Formula body) => Disp(new Formula.Bind(
        FormulaQuantifier.ForAll,
        FormulaIdentifier.Create("n"),
        Naturals(),
        body));

    private static Formula DivisorSum(Formula index, Formula n, Formula summand) =>
        Seq(
            new Formula.Subscript(
                Sum,
                Seq(index, Sp, InMacro, Sp, Call("divisors", n))),
            Sp,
            summand);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
}
