using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class GreathouseLogTwoFloorRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/GreathouseLogTwoFloorRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/greathouse2012a175406");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The OEIS A175406 floor formula is refuted at a large explicit index.",
        H("The OEIS A175406 Greathouse Floor Formula"),
        Blocks(
            Describe.Lean(DescribeId.Create("a175406-sequence-value"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The greatest admissible exponent"),
                StatementSource.FromAuthor(AFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For each natural n, a(n) is the supremum of the natural exponents "
                        + "whose real power of 1 + 1/n is at most 2. The cast (n : R) is "
                        + "the real-number cast used in the Lean definition. In the natural "
                        + "conditionally complete order, sSup of an unbounded set is 0, so "
                        + "this definition is total."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a175406-floor-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Greathouse's floor conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural n with 1 <= n, the conjecture identifies a(n) "
                        + "with the natural floor of (n + 1/2) times Real.log 2. The "
                        + "symbol shown as floor with a subscript plus is Nat.floor."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a175406-floor-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The floor conjecture is false"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At n0 = 1121626023352383, let M = 777451915729368. The certified "
                        + "log-series estimates give the stated natural floor as M, while "
                        + "the defining supremum is M - 1: the M-th power is greater than 2 "
                        + "and the (M - 1)-st power is at most 2. The proof uses 36 positive "
                        + "terms and a geometric tail for log 2, two positive terms for the "
                        + "witness logarithm, and log(1+x) <= x. No minimality claim is made."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a175406-log-two-floor-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula AFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var nReal = Coerce(n, Reals());
        var baseValue = Add(D(1), new Formula.Fraction(D(1), nReal));
        var predicate = new Formula.Relation(
            new Formula.Power(baseValue, k),
            FormulaRelationOperator.LessThanOrEqual,
            D(2));
        var set = Seq(OpenBrace, k, Sp, InMacro, Sp, Naturals(), Sp, Bar, Sp,
            predicate, CloseBrace);
        return Disp(ForAll("n", Naturals(),
            Equal(Call("a", n), Call("sSup", set))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var nReal = Coerce(n, Reals());
        var half = new Formula.Fraction(D(1), D(2));
        var floorValue = Seq(
            Lfloor,
            Multiply(Add(nReal, half), QualifiedCall("Real", "log", D(2))),
            Rfloor,
            Underscore,
            Plus);
        var premise = new Formula.Relation(
            D(1), FormulaRelationOperator.LessThanOrEqual, n);
        var conclusion = Equal(Call("a", n), floorValue);
        var quantified = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            new Formula.Logic(
                Parenthesized(premise),
                FormulaLogicOperator.Implies,
                Parenthesized(conclusion)));
        return Disp(new Formula.Logic(
            Parenthesized(F.Id("claim")),
            FormulaLogicOperator.Iff,
            Parenthesized(quantified)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula Coerce(Formula value, Formula type) =>
        Parenthesized(Seq(value, Sp, Colon, Sp, type));

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name), domain, body);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Reals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Real"));

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);
}
