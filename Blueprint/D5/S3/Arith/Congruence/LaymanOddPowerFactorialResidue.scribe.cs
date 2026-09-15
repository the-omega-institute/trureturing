using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class LaymanOddPowerFactorialResidueDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Arith/Congruence/LaymanOddPowerFactorialResidue.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/lava2010a119690");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Odd powers of a factorial have Layman's classified residue modulo the corresponding triangular number.",
        H("Layman's Odd-Power Factorial Residue"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a119690-factorial-divisibility"),
                DeclarationHandle.Create(
                    Prefix + "factorial_dvd_triangular_of_not_odd_prime"),
                H("Factorial divisibility outside the odd-prime branch"),
                StatementSource.FromAuthor(DivisibilityFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least one, if n+1 is not an odd prime, "
                        + "then the triangular number n(n+1)/2 divides n!. This is a "
                        + "general-purpose reusable lemma with the residue theorem as "
                        + "its first consumer. In the even-n, odd-composite-successor "
                        + "case, a factorization n+1=a*b and parity give a+b<a*b, "
                        + "including when a=b. The embedding a!*b! divides (a+b)! and "
                        + "then n!, followed by coprime combination with n/2, proves "
                        + "the required divisibility."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("a119690-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Layman's odd-power residue classification"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For all natural n at least one and every natural k, the odd power "
                        + "(n!)^(2k+1) modulo n(n+1)/2 is n exactly in the odd-prime "
                        + "successor branch and is zero otherwise. In the prime branch, "
                        + "Wilson's theorem gives residue minus one modulo n+1, while "
                        + "factorial divisibility gives residue zero modulo n/2. Their "
                        + "coprime product combines these residues, and an odd power "
                        + "preserves both. The other branch uses the divisibility lemma."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a119690-layman-odd-power-factorial-residue"),
                    ResolutionKind.Proved)))));

    private static Formula DivisibilityFormula()
    {
        var n = F.Id("n");
        var successor = Add(n, D(1));
        var oddPrime = And(Prime(successor), Call("Odd", successor));
        var hypotheses = And(
            LessOrEqual(D(1), n),
            new Formula.Not(Parenthesized(oddPrime)));
        return Disp(Universal(["n"], Implies(
            Parenthesized(hypotheses),
            Parenthesized(Divides(Triangular(n), Factorial(n))))));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var successor = Add(n, D(1));
        var exponent = Add(Multiply(D(2), k), D(1));
        var residue = new Formula.Modulo(
            Power(Factorial(n), exponent), Parenthesized(Triangular(n)));
        var classified = IfThenElse(
            And(Prime(successor), Call("Odd", successor)), n, D(0));
        return Disp(Universal(["n", "k"], Implies(
            LessOrEqual(D(1), n),
            Parenthesized(Equal(residue, classified)))));
    }

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Universal(string[] names, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [.. names.Select(name =>
                new Formula.BoundVariable(FormulaIdentifier.Create(name), Naturals()))],
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Prime(Formula value) => Call("Prime", value);

    private static Formula Triangular(Formula n) => Divide(
        Multiply(n, Parenthesized(Add(n, D(1)))), D(2));

    private static Formula Factorial(Formula value) => Seq(value, Bang);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));

    private static Formula IfThenElse(
        Formula predicate, Formula whenTrue, Formula whenFalse) =>
        Parenthesized(Seq(
            Named("if"), Sp, Parenthesized(predicate), Sp,
            Named("then"), Sp, whenTrue, Sp,
            Named("else"), Sp, whenFalse));

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Divide(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Slash, Sp, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
