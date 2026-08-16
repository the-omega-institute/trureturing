using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisot;

internal sealed class Beta13Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var beta = Id("beta13");
        var conjugate = Id("beta13Conjugate");
        var quadratic = Equal(new Formula.Power(beta, Num(2)), Add(beta, Num(3)));
        var conjugateOutsideUnit = new Formula.Relation(
            new Formula.Absolute(conjugate),
            FormulaRelationOperator.GreaterThan,
            Num(1));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The quadratic base beta13 has a conjugate outside the open unit disk.",
            H("The Quadratic Base Beta13"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("beta13-quadratic-identity"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13.beta13_sq"),
                    H("Beta13 satisfies its quadratic equation"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(quadratic)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Squaring the radical definition and using sqrt(13)^2 = 13 gives "
                            + "beta13 squared equal to beta13 plus three."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("beta13-conjugate-outside-unit-disk"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13.beta13_conjugate_abs_gt_one"),
                    H("The conjugate lies outside the unit disk"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(conjugateOutsideUnit)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The conjugate is negative, and sqrt(13) is greater than three, "
                            + "so its absolute value is strictly greater than one."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("beta13-is-irrational"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/NonPisot/Beta13.beta13_irrational"),
                    H("Beta13 is irrational"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(Call("Irrational", beta))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Mathlib's irrationality theorem for the square root of a prime "
                            + "passes through the nonzero rational affine transformation."))),
                    DescribeRole.Theorem))));
    }
}
