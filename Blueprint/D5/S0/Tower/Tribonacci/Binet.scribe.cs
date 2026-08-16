using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.Tribonacci;

internal sealed class TribonacciBinetDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var a = Id("a");
        var n = Id("n");
        var t = Id("t");
        var z = Id("z");
        var naturals = Id("N");
        var complexes = Id("C");
        var coefficient = new Formula.Fraction(
            new Formula.Power(t, Num(2)),
            Add(
                Add(new Formula.Power(t, Num(2)), Multiply(Num(2), t)),
                Num(3)));
        var remainder = new Formula.Sequence(
            Subtract(
                Call("T", n),
                Multiply(a, new Formula.Power(t, n))),
            n,
            naturals);
        var cubic = Equal(
            new Formula.Power(z, Num(3)),
            Add(Add(new Formula.Power(z, Num(2)), z), Num(1)));
        var secondaryRootBound = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("z"),
            complexes,
            new Formula.Logic(
                new Formula.Logic(
                    cubic,
                    FormulaLogicOperator.And,
                    NotEqual(z, t)),
                FormulaLogicOperator.Implies,
                new Formula.Relation(
                    Call("abs", z),
                    FormulaRelationOperator.LessThan,
                    Num(1))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The Tribonacci recurrence has an exact Perron coefficient "
            + "and bounded secondary roots.",
            H("Tribonacci Binet Coefficient"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("exact-tribonacci-binet-coefficient"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Binet.tribonacciBinetCoefficient"),
                    H("Exact Perron coefficient"),
                    StatementSource.FromAuthor(Equal(a, coefficient)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The initial values zero, one, one select t squared divided by "
                        + "t squared plus two t plus three as the coefficient of t to the n."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("tribonacci-binet-remainder-tends-to-zero"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Binet.tribonacci_binet_tendsto_zero"),
                    H("The exact Binet remainder tends to zero"),
                    StatementSource.FromAuthor(Equal(
                        Call("limitAtTop", remainder),
                        Num(0))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Applying the residual quadratic factor isolates the Perron mode. "
                        + "The remaining term is an exact fixed linear combination of two "
                        + "consecutive frozen Perron errors, so it converges to zero."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-secondary-roots-inside-unit-disk"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/Tribonacci/Binet."
                        + "abs_lt_one_of_tribonacci_root_ne_perron"),
                    H("Secondary roots lie inside the unit disk"),
                    StatementSource.FromAuthor(secondaryRootBound),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Removing the Perron factor leaves a real quadratic. Its negative "
                        + "discriminant forces each secondary root to be nonreal, while its "
                        + "real and imaginary equations give squared modulus t inverse, "
                        + "which is strictly below one."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/PerronRoot")),
            ]));
    }
}
