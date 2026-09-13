using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class GerasimovTwinPrimeMeanNoSuperdivisorDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/GerasimovTwinPrimeMeanNoSuperdivisor.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/gerasimov2015a254748");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twin-prime pair averages have no superdivisor.",
        H("The A254748 Twin-Prime Mean Conjecture"),
        Blocks(
            Node("IsSuperdivisor", "The A247477 superdivisor predicate", IsSuperdivisorFormula(),
                "For natural n and k, the three displayed divisibility conditions define a "
                    + "superdivisor. The slash is natural-number division, and it agrees with "
                    + "the exact quotient when k divides n.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gerasimov_a254748", "The twin-prime mean theorem", TheoremFormula(),
                "For twin primes p and p+2, every positive divisor k of p+1 fails the "
                    + "superdivisor predicate. The proof uses the multiplicative order in "
                + "ZMod (k+1), through the stronger statement for an even n at least 4 "
                    + "whose predecessor is prime.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a254748-twin-prime-mean-no-superdivisor"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a254748-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula IsSuperdivisorFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var quotient = NatDiv(n, k);
        var modulus = Add(quotient, n);
        var conditions = And(
            Divides(modulus, Add(Power(Parenthesized(quotient), quotient), n)),
            And(
                Divides(modulus, Add(Power(Parenthesized(quotient), n), quotient)),
                Divides(modulus, Add(Power(n, quotient), quotient))));
        return Disp(ForAll([Bound("n"), Bound("k")],
            Iff(Call("IsSuperdivisor", n, k), Parenthesized(conditions))));
    }

    private static Formula TheoremFormula()
    {
        var p = F.Id("p");
        var k = F.Id("k");
        var twinPrime = Implies(
            Prime(p),
            Implies(
                Prime(Add(p, D(2))),
                ForAll([Bound("k")],
                    Implies(
                        LessOrEqual(D(1), k),
                        Implies(
                            Divides(k, Add(p, D(1))),
                            new Formula.Not(Call(
                                "IsSuperdivisor", Add(p, D(1)), k)))))));
        return Disp(ForAll([Bound("p")], twinPrime));
    }

    private static Formula.BoundVariable Bound(string name) => new Formula.BoundVariable(
        FormulaIdentifier.Create(name), Naturals());

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll,
        [.. variables],
        body);

    private static Formula Naturals() => new Formula.LatexGroup([Mathbb, Sp, F.Id("N")]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Prime(Formula value) => Call("Prime", value);

    private static Formula NatDiv(Formula left, Formula right) =>
        Seq(left, Sp, Slash, Sp, right);

    private static Formula Power(Formula basis, Formula exponent) =>
        new Formula.Power(basis, exponent);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
