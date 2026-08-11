using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower;

internal sealed class ConstantArmsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var b = Id("b");
        var q = Id("Q");
        var m = Id("m");
        var naturals = Id("N");
        var scale = new Formula.Power(b, q);
        var denominator = Add(b, Num(1));
        var unitPoint = new Formula.Fraction(Num(1), denominator);
        var evenPoint = new Formula.Fraction(new Formula.Fraction(b, Num(2)), denominator);
        var baseAssumptions = new Formula.Logic(
            new Formula.Relation(b, FormulaRelationOperator.GreaterThanOrEqual, Num(2)),
            FormulaLogicOperator.And,
            new Formula.Relation(q, FormulaRelationOperator.GreaterThanOrEqual, Num(1)));

        Formula ArmEquation(Formula point, Formula arm) => Equal(
            Multiply(scale, Call("radixDistance", b, q, point)),
            arm);

        Formula ForBases(Formula assumptions, Formula equation) =>
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [
                    new Formula.BoundVariable(FormulaIdentifier.Create("b"), naturals),
                    new Formula.BoundVariable(FormulaIdentifier.Create("Q"), naturals),
                ],
                new Formula.Logic(assumptions, FormulaLogicOperator.Implies, equation));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Radix name towers have exact normalized approximation arms at canonical rational points.",
            H("Radix Constant Arms"),
            Blocks(
                Paragraph(Text(
                    "At level Q, the radix grid consists of integer multiples of the inverse "
                    + "scale. Its distance is realized by scaling, rounding to a nearest integer, "
                    + "and dividing by the scale.")),
                new DocumentBlock.DisplayFormula(Equal(
                    Call("D", b, q),
                    new Formula.SetBuilder(new Formula.Fraction(m, scale), m, new Formula.Integers()))),
                new DocumentBlock.DisplayFormula(Equal(
                    Call("radixDistance", b, q, Id("x")),
                    new Formula.Fraction(
                        new Formula.Absolute(Subtract(
                            Multiply(scale, Id("x")),
                            Call("round", Multiply(scale, Id("x"))))),
                        scale))),
                Describe.Lean(
                    DescribeId.Create("reciprocal-point-has-a-constant-arm"),
                    DeclarationHandle.Create("D5/S0/Tower/ConstantArms.constant_arm"),
                    H("The reciprocal point has a constant arm"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(ForBases(
                        baseAssumptions,
                        ArmEquation(unitPoint, unitPoint)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every radix b at least two and every level Q at least one, the "
                        + "normalized distance from 1 divided by b plus one to the radix grid is "
                        + "exactly 1 divided by b plus one. The proof uses the power congruence "
                        + "b congruent to minus one modulo b plus one and mathlib's exact nearest "
                        + "integer rounding formula."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("even-half-radix-point-has-a-constant-arm"),
                    DeclarationHandle.Create("D5/S0/Tower/ConstantArms.even_champion_arm"),
                    H("The even half-radix point has a constant arm"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(ForBases(
                        new Formula.Logic(
                            baseAssumptions,
                            FormulaLogicOperator.And,
                            Call("Even", b)),
                        ArmEquation(
                            evenPoint,
                            new Formula.Fraction(b, Multiply(Num(2), denominator)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "When b is even, the point b over two times b plus one has normalized "
                        + "distance b over two times b plus one at every positive level. Its two "
                        + "possible residues are the two central residues around half the odd "
                        + "modulus b plus one."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("binary-one-third-is-the-radix-two-specialization"),
                    DeclarationHandle.Create("D5/S0/Tower/ConstantArms.binary_arm"),
                    H("Binary one-third is the radix-two specialization"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("Q"),
                        naturals,
                        new Formula.Logic(
                            new Formula.Relation(
                                q,
                                FormulaRelationOperator.GreaterThanOrEqual,
                                Num(1)),
                            FormulaLogicOperator.Implies,
                            Equal(
                                Multiply(
                                    new Formula.Power(Num(2), q),
                                    Call(
                                        "radixDistance",
                                        Num(2),
                                        q,
                                        new Formula.Fraction(Num(1), Num(3)))),
                                new Formula.Fraction(Num(1), Num(3))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The binary identity is obtained only by specializing the general "
                        + "reciprocal-point theorem to radix two; it has no independent proof."))),
                    DescribeRole.Theorem))));
    }
}
