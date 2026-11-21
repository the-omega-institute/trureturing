using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Kozlov;

internal sealed class EqualShiftDivisibilityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Convexity/snellman2026kozlov");
    private const string Prefix = "D5/S3/Combinatorics/Kozlov/EqualShiftDivisibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every positive ground-set size, the proper-sum and real-dilate lattice counts each extend to a rational polynomial. Their difference vanishes at zero and minus one.",
        H("The equal-shift Kozlov deficiency factor"),
        Blocks(
            Node("agreesonpositiveranks", "AgreesOnPositiveRanks", "Agreement with a literal count at positive ranks", DescribeRole.Definition,
                "For every positive natural rank, the rational evaluation equals the natural count cast to the rationals.", Agreement()),
            Node("equal-shift-count-polynomials-exist", "equal_shift_count_polynomials_exist", "Both literal counts have rational interpolants", DescribeRole.Theorem,
                "Part III, Corollary 34, states polynomiality of both counts and credits Part II, Theorems 36 and 41, for the proper count and its transfer formula. Here the rational witnesses come from the two falling-binomial matrix polynomials composed with X+1. The unconditional proper and lattice transfer laws identify each entry of power r+1 with its literal count at every positive rank r.", Existence()),
            Node("equal-shift-kozlov-deficiency-divisible", "equal_shift_kozlov_deficiency_divisible", "Divisibility by X times X plus one", DescribeRole.Theorem,
                "Infinitely many positive natural ranks identify each interpolant with its matrix polynomial. At argument zero the relevant power is one and the first-to-last entry is one in each matrix. At argument minus one the relevant power is zero, so the identity entry is one when n=1 and zero otherwise. Thus the difference has both roots, giving the product of the two factors. This proves the divisibility question in Part III, Section 10 item 2.", Divisibility(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("snellman-equal-shift-kozlov-deficiency"), ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string name, string title, DescribeRole role, string prose, Formula? formula = null,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("kozlov-equal-shift-divisibility-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            name == "equal_shift_count_polynomials_exist"
                ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Natural() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Rational() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Polynomials() => Seq(Rational(), OpenBracket, F.Id("X"), CloseBracket);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula domain, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), domain, body);
    private static Formula Positive(string name) =>
        new Formula.Relation(D(0), FormulaRelationOperator.LessThan, F.Id(name));
    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);
    private static Formula Counts(Formula proper, Formula lattice) =>
        new Formula.Logic(proper, FormulaLogicOperator.And, lattice);
    private static Formula EqualsCount(string polynomial, string count) =>
        new Formula.Relation(Call(polynomial, F.Id("r")), FormulaRelationOperator.Equal,
            Call("rat", Call(count, F.Id("n"), F.Id("r"))));
    private static Formula Matches(string polynomial, string count) =>
        Bind(FormulaQuantifier.ForAll, "r", Natural(), Implies(Positive("r"), EqualsCount(polynomial, count)));
    private static Formula OverGroundSize(Formula body) =>
        Bind(FormulaQuantifier.ForAll, "n", Natural(), Implies(Positive("n"), body));

    private static Formula Agreement() => Disp(new Formula.Logic(
        Call("AgreesOnPositiveRanks", F.Id("P"), F.Id("c")), FormulaLogicOperator.Iff,
        Bind(FormulaQuantifier.ForAll, "r", Natural(), Implies(Positive("r"),
            new Formula.Relation(Call("P", F.Id("r")), FormulaRelationOperator.Equal,
                Call("rat", Call("c", F.Id("r"))))))));

    private static Formula Existence() => Disp(OverGroundSize(
        Bind(FormulaQuantifier.Exists, "A", Polynomials(),
            Bind(FormulaQuantifier.Exists, "L", Polynomials(),
                Counts(Matches("A", "properCount"), Matches("L", "latticeCount"))))));

    private static Formula Divisibility()
    {
        var x = F.Id("X");
        var factor = new Formula.Binary(x, FormulaBinaryOperator.Multiply,
            Seq(Open, new Formula.Binary(x, FormulaBinaryOperator.Add, D(1)), Close));
        var difference = new Formula.Binary(F.Id("L"), FormulaBinaryOperator.Subtract, F.Id("A"));
        return Disp(OverGroundSize(Bind(FormulaQuantifier.ForAll, "A", Polynomials(),
            Bind(FormulaQuantifier.ForAll, "L", Polynomials(),
                Implies(Matches("A", "properCount"), Implies(Matches("L", "latticeCount"),
                    new Formula.Relation(factor, FormulaRelationOperator.Divides, difference)))))));
    }
}
