using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class FiroozbakhtLeastSelfDivisorPowerMinusOneDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/FiroozbakhtLeastSelfDivisorPowerMinusOne.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Factorization/firoozbakht2004a092028");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The least self-divisor exponent in OEIS A092028 is the least prime factor of n minus one.",
        H("The Least Self-Divisor Exponent"),
        Blocks(
            Node("a", "The A092028 sequence", DefinitionFormula(),
                "In the natural numbers, `sInf` selects the least element of the set, and `sInf` "
                + "of the empty set is zero. For n greater "
                + "than two, the defining set is nonempty. Every subtraction in the formula "
                + "is truncated natural-number subtraction.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("firoozbakht_a092028", "Firoozbakht's second conjecture", TheoremFormula(),
                "The upper bound uses p=minFac(n-1), since p divides n-1 and therefore p divides "
                + "n^p-1. For the lower bound, take q=minFac(m). The multiplicative order of n "
                + "modulo q divides both m and q-1; minimality of q makes those integers coprime, "
                + "so the order is one and q divides n-1. Firoozbakht's first conjecture follows "
                + "because minFac(n-1) is prime when n is greater than two.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a092028-least-self-divisor-power-minus-one"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a092028-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula DefinitionFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var greaterThanOne = Relation(D(1), FormulaRelationOperator.LessThan, m);
        var divides = Relation(m, FormulaRelationOperator.Divides,
            Subtract(Power(n, m), D(1)));
        var conditions = new Formula.Logic(
            Parenthesized(greaterThanOne), FormulaLogicOperator.And, Parenthesized(divides));
        var witnesses = Seq(OpenBrace, m, Sp, InMacro, Sp, Naturals(), Sp, Mid, Sp,
            conditions, CloseBrace);
        return Disp(Universal("n", Equal(Call("a", n), Call("sInf", witnesses))));
    }

    private static Formula TheoremFormula()
    {
        var n = F.Id("n");
        var hypothesis = Relation(D(2), FormulaRelationOperator.LessThan, n);
        var conclusion = Equal(Call("a", n), Call("minFac", Subtract(n, D(1))));
        return Disp(Universal("n", new Formula.Logic(
            Parenthesized(hypothesis), FormulaLogicOperator.Implies,
            Parenthesized(conclusion))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Universal(string variable, Formula body) => new Formula.Bind(
        FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Relation(Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);
    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
