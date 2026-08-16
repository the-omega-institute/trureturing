using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class DBonacciGeneralChampionValueDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var beta = Id("beta");
        var t = Id("t");
        var phi = Id("phi");
        var b3 = Id("b3");
        var b4 = Id("b4");
        var b5 = Id("b5");
        var reals = Id("R");
        var minusOne = Subtract(Num(0), Num(1));
        var million = Num(1000000);
        var tolerance = new Formula.Fraction(Num(1), million);

        Formula Value(Formula root) => new Formula.Fraction(
            Subtract(Subtract(new Formula.Power(root, Num(2)), root), Num(1)),
            Subtract(new Formula.Power(root, Num(2)), Num(1)));

        Formula Initial(Formula root) => new Formula.Fraction(
            Subtract(Num(1), new Formula.Power(root, minusOne)),
            Num(2));

        Formula NumericCertificate(Formula root, int numerator) =>
            new Formula.Relation(
                Call(
                    "abs",
                    Subtract(
                        Call("championValue", root),
                        new Formula.Fraction(Num(numerator), million))),
                FormulaRelationOperator.LessThan,
                tolerance);

        var definition = Equal(Call("championValue", beta), Value(beta));
        var tribonacciIdentity = Equal(Call("championValue", t), Initial(t));
        var goldenNumerator = Equal(
            Subtract(Subtract(new Formula.Power(phi, Num(2)), phi), Num(1)),
            Num(0));
        var goldenValue = Equal(Call("championValue", phi), Num(0));
        var endpointValue = Equal(
            Call("championValue", Num(2)),
            new Formula.Fraction(Num(1), Num(3)));
        var cubic = Equal(
            new Formula.Power(beta, Num(3)),
            Add(Add(new Formula.Power(beta, Num(2)), beta), Num(1)));
        var coincidence = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("beta"),
            reals,
            new Formula.Logic(
                new Formula.Relation(Num(1), FormulaRelationOperator.LessThan, beta),
                FormulaLogicOperator.Implies,
                new Formula.Logic(
                    Equal(Initial(beta), Call("championValue", beta)),
                    FormulaLogicOperator.Iff,
                    cubic)));
        var fiveRefutation = NotEqual(Initial(b5), Call("championValue", b5));
        var numericThree = NumericCertificate(b3, 228155);
        var numericFour = NumericCertificate(b4, 290162);
        var numericFive = NumericCertificate(b5, 313794);

        return DocumentDefinition.Create(ScribeNode.Create(
            "The corrected d-bonacci champion expression has exact Tribonacci, golden-ratio, "
                + "endpoint, and low-order numerical checks.",
            H("D-Bonacci Champion Value"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("corrected-d-bonacci-champion-value"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue"),
                    H("Corrected algebraic value"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(definition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For d-bonacci champion claims this expression is used only for orders "
                            + "d at least three. Its order-two evaluation is recorded separately "
                            + "and is not identified with the degenerate-phase tower value."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("tribonacci-coincidence-identity"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionValue."
                        + "championValue_tribonacciConstant"),
                    H("The two Tribonacci expressions coincide"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(tribonacciIdentity)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The Tribonacci cubic reduces the corrected rational expression to the "
                            + "frozen low arm. A companion theorem rewrites the existing period-two "
                            + "liminf directly as championValue(t)."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-ratio-numerator-zero"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionValue."
                        + "goldenRatio_championValue_numerator"),
                    H("The order-two numerator vanishes"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(goldenNumerator)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is exactly the quadratic equation phi squared equals phi plus one."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-ratio-corrected-value-zero"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionValue."
                        + "championValue_goldenRatio"),
                    H("The corrected expression is zero at phi"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(goldenValue)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Zero is the value of this rational expression, not the distinct "
                            + "degenerate-phase champion value."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("endpoint-value-one-third"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionValue.championValue_two"),
                    H("The endpoint weld is one third"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(endpointValue)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Direct substitution at beta equal to two gives the exact value one third."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-cubic-is-the-coincidence-locus"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionValue."
                        + "initialFormula_eq_championValue_iff"),
                    H("The initial formula coincides exactly on the Tribonacci cubic"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(coincidence)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every real beta above one, equality of the initial and corrected "
                            + "expressions is equivalent to the Tribonacci cubic equation."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("order-five-initial-formula-refuted"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionValue."
                        + "dbonacci_five_initial_formula_ne_championValue"),
                    H("The initial formula fails at order five"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(fiveRefutation)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Strict growth of the d-bonacci Perron roots excludes the order-five root "
                            + "from the Tribonacci coincidence locus."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("order-three-value-numeric-certificate"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionValue."
                        + "championValue_three_numeric"),
                    H("Order-three numerical certificate"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(numericThree)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact value differs from 0.228155 by less than one millionth."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("order-four-value-numeric-certificate"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionValue."
                        + "championValue_four_numeric"),
                    H("Order-four numerical certificate"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(numericFour)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact value differs from 0.290162 by less than one millionth."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("order-five-value-numeric-certificate"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/ChampionValue."
                        + "championValue_five_numeric"),
                    H("Order-five numerical certificate"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(numericFive)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The exact value differs from 0.313794 by less than one millionth."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/PerronRoot")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Tribonacci/ChampionOrbit")),
            ]));
    }
}
