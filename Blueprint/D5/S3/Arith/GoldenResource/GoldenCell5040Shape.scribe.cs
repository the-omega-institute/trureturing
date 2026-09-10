using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenCell5040ShapeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenCell5040Shape.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The power residue condition pins four prime exponents and leaves a coprime factor.",
        H("Prime Exponent Windows From The Residue"),
        Blocks(
            Paragraph(Text("Suppose the index is divisible by 5040 and the power of three with "
                + "that index leaves residue 2241. The lower bounds on the exponents of two and "
                + "three come from the divisibility alone. The upper bounds, and the exponents "
                + "of five, seven and eighty three, come from five separate small modulus "
                + "arguments, each of which contradicts the residue.")),
            Paragraph(Text("Indices and exponents are natural numbers. The residue condition is "
                + "read modulo the index itself. The multiplicative orders used below are of "
                + "three, in the units modulo 128, 25 and 49 respectively. Note that this does "
                + "not pin the remaining factor: it says only that the remaining factor shares "
                + "no prime with two, three, five, seven or eighty three.")),
            Node("modEq_2241_factorization", "Four exponents are determined", FactorizationFormula(),
                "Divisibility by 5040 gives the two lower bounds. For the upper bound on two, a "
                + "seventh power of two in the index would make the index divisible by the order "
                + "of three modulo 128, forcing residue one there, while 2241 leaves 65. For "
                + "three, a fourth power would make the power of three vanish modulo 81, while "
                + "2241 leaves 54. For five and seven the orders 20 and 42 already divide 5040, "
                + "so a square of either prime would force residue one against 16 and 36. "
                + "Finally eighty three divides 2241 but never divides a power of three, so it "
                + "cannot divide the index.",
                DescribeRole.Lemma),
            Node("modEq_2241_shape", "The index has a coprime residual factor", ShapeFormula(),
                "Split the index at the four determined primes. The quotient is a natural "
                + "number sharing no prime factor with them, nor with eighty three, because each "
                + "of those exponents was already fixed. The exponent windows carry over "
                + "unchanged. The residual factor is not claimed to be one: indices with a "
                + "larger coprime factor also satisfy the residue condition.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role) => Describe.Lean(
        DescribeId.Create("cell-5040-shape-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Hyp() => Seq(
        D(5,0,4,0), Sp, Mid, Sp, N(), Sp, Land, Sp,
        new Formula.Power(D(3), N()), Sp, Equiv, Sp, D(2,2,4,1), Sp,
        Open, Mathrm, Grp(F.Id("mod")), Sp, N(), Close);

    private static Formula FactorizationFormula() => Disp(Seq(NatBound("n"), Sp,
        Hyp(), Sp, Implies, Sp,
        D(4), Sp, Le, Sp, V(D(2)), Sp, Le, Sp, D(6), Sp, Land, Sp,
        D(2), Sp, Le, Sp, V(D(3)), Sp, Le, Sp, D(3), Sp, Land, Sp,
        V(D(5)), Sp, Eq, Sp, D(1), Sp, Land, Sp,
        V(D(7)), Sp, Eq, Sp, D(1), Sp, Land, Sp,
        V(D(8,3)), Sp, Eq, Sp, D(0)));

    private static Formula ShapeFormula() => Disp(Seq(NatBound("n"), Sp,
        Hyp(), Sp, Implies, Sp, Exists, Sp,
        F.Id("a"), Comma, Sp, F.Id("b"), Comma, Sp, F.Id("r"), Sp, InMacro, Sp,
        Mathbb, Grp(F.Id("N")), Comma, Sp,
        N(), Sp, Eq, Sp,
        Mul(Mul(Mul(Mul(new Formula.Power(D(2), F.Id("a")),
            new Formula.Power(D(3), F.Id("b"))), D(5)), D(7)), F.Id("r")), Sp, Land, Sp,
        D(4), Sp, Le, Sp, F.Id("a"), Sp, Le, Sp, D(6), Sp, Land, Sp,
        D(2), Sp, Le, Sp, F.Id("b"), Sp, Le, Sp, D(3), Sp, Land, Sp,
        Call("gcd", F.Id("r"), D(1,7,4,3,0)), Sp, Eq, Sp, D(1)));

    private static Formula V(Formula p) => Call("v", p, N());
    private static Formula N() => F.Id("n");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Mul(Formula x, Formula y) =>
        new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula NatBound(string name) => Seq(Forall, Sp, F.Id(name), Sp,
        InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma);
}
