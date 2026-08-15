using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.MetricGeometry;

internal sealed class RadixGridDistanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var b = Id("b");
        var q = Id("Q");
        var m = Id("m");
        var x = Id("x");
        var naturals = Id("N");
        var integers = Id("Z");
        var reals = Id("R");
        var binaryScale = new Formula.Power(Num(2), q);
        var oneThird = new Formula.Fraction(Num(1), Num(3));
        var binaryGrid = Call("radixGrid", Num(2), q);
        var binaryInfDist = Call("infDist", oneThird, binaryGrid);
        var residual = new Formula.Absolute(Subtract(binaryScale, Multiply(Num(3), m)));

        Formula ForAllQ(Formula body) => new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("Q"),
            naturals,
            body);

        Formula AndAll(params Formula[] items)
        {
            var result = items[^1];
            for (var index = items.Length - 2; index >= 0; index--)
            {
                result = new Formula.Logic(items[index], FormulaLogicOperator.And, result);
            }
            return result;
        }

        return DocumentDefinition.Create(ScribeNode.Create(
            "Radix rounding distance equals metric distance to the radix grid.",
            H("Radix Grid Distance"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("rounding-realizes-radix-grid-distance"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/RadixGridDistance."
                        + "radixDistance_eq_infDist"),
                    H("Rounding realizes radix-grid distance"),
                    StatementSource.FromAuthor(new Formula.BindMany(
                        FormulaQuantifier.ForAll,
                        [
                            new Formula.BoundVariable(FormulaIdentifier.Create("b"), naturals),
                            new Formula.BoundVariable(FormulaIdentifier.Create("Q"), naturals),
                        ],
                        new Formula.Logic(
                            NotEqual(b, Num(0)),
                            FormulaLogicOperator.Implies,
                            new Formula.Bind(
                                FormulaQuantifier.ForAll,
                                FormulaIdentifier.Create("x"),
                                reals,
                                Equal(
                                    Call("radixDistance", b, q, x),
                                    Call("infDist", x, Call("radixGrid", b, q))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every nonzero radix and every level, scaling and rounding to "
                                + "a nearest integer gives exactly the metric infimum distance "
                                + "from the point to the corresponding radix grid.")),
                        Paragraph(Text(
                            "The lower bound applies Metric.le_infDist and round_le to every "
                                + "grid point. The rounded integer supplies a grid member for "
                                + "the reverse bound through Metric.infDist_le_dist_of_mem."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("binary-point-distance-numerator-formula"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/RadixGridDistance."
                        + "binary_point_distance_formula"),
                    H("Binary point distances have the integer numerator formula"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Bind(
                        FormulaQuantifier.ForAll,
                        FormulaIdentifier.Create("m"),
                        integers,
                        Equal(
                            new Formula.Absolute(Subtract(
                                oneThird,
                                new Formula.Fraction(m, binaryScale))),
                            new Formula.Fraction(
                                residual,
                                Multiply(Num(3), binaryScale)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For every binary level and integer grid index m, the pointwise "
                            + "distance from one third to m divided by two to that level is "
                            + "the absolute integer residual divided by three times the scale."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("binary-powers-are-nonzero-modulo-three"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/RadixGridDistance."
                        + "binary_pow_mod_three_ne_zero"),
                    H("Binary powers are nonzero modulo three"),
                    StatementSource.FromAuthor(ForAllQ(NotEqual(
                        Call("mod", binaryScale, Num(3)),
                        Num(0)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "If a power of two were zero modulo three, primality would force "
                            + "three to divide two. Pinned mathlib supplies the exact "
                            + "prime-divides-a-power implication used for that contradiction."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("binary-integer-residual-minimum-is-one"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/RadixGridDistance."
                        + "binary_integer_residual_minimum"),
                    H("The binary integer residual minimum is one"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Logic(
                        new Formula.Bind(
                            FormulaQuantifier.Exists,
                            FormulaIdentifier.Create("m"),
                            integers,
                            Equal(residual, Num(1))),
                        FormulaLogicOperator.And,
                        new Formula.Bind(
                            FormulaQuantifier.ForAll,
                            FormulaIdentifier.Create("m"),
                            integers,
                            new Formula.Relation(
                                residual,
                                FormulaRelationOperator.GreaterThanOrEqual,
                                Num(1)))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "An induction constructs an integer index whose residual is plus or "
                            + "minus one. If any residual vanished, the preceding nonzero "
                            + "modulo three result would be contradicted, so every absolute "
                            + "residual is at least one."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("binary-one-third-distance-to-the-actual-grid"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/RadixGridDistance."
                        + "binary_grid_distance"),
                    H("Binary one third has exact distance to the actual grid"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Logic(
                        new Formula.Relation(
                            q,
                            FormulaRelationOperator.GreaterThanOrEqual,
                            Num(1)),
                        FormulaLogicOperator.Implies,
                        new Formula.Logic(
                            Equal(Multiply(binaryScale, binaryInfDist), oneThird),
                            FormulaLogicOperator.And,
                            Equal(
                                binaryInfDist,
                                new Formula.Fraction(
                                    Num(1),
                                    Multiply(Num(3), binaryScale))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "At every positive binary level, two to the level times the "
                                + "metric infimum distance from one third to the radix grid is "
                                + "one third, and the unscaled distance is one divided by three "
                                + "times that power of two.")),
                        Paragraph(Text(
                            "This applies the frozen binary arm computation through the public "
                                + "rounding-to-grid bridge; it does not restate or reprove that "
                                + "frozen theorem."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("all-binary-constant-arm-clauses"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/MetricGeometry/RadixGridDistance."
                        + "binary_constant_arm_clauses"),
                    H("All binary constant-arm clauses"),
                    StatementSource.FromAuthor(ForAllQ(new Formula.Logic(
                        new Formula.Relation(
                            q,
                            FormulaRelationOperator.GreaterThanOrEqual,
                            Num(1)),
                        FormulaLogicOperator.Implies,
                        AndAll(
                            Call("Coprime", Num(3), Num(2)),
                            new Formula.Bind(
                                FormulaQuantifier.ForAll,
                                FormulaIdentifier.Create("m"),
                                integers,
                                Equal(
                                    new Formula.Absolute(Subtract(
                                        oneThird,
                                        new Formula.Fraction(m, binaryScale))),
                                    new Formula.Fraction(
                                        residual,
                                        Multiply(Num(3), binaryScale)))),
                            NotEqual(Call("mod", binaryScale, Num(3)), Num(0)),
                            new Formula.Bind(
                                FormulaQuantifier.Exists,
                                FormulaIdentifier.Create("m"),
                                integers,
                                Equal(residual, Num(1))),
                            new Formula.Bind(
                                FormulaQuantifier.ForAll,
                                FormulaIdentifier.Create("m"),
                                integers,
                                new Formula.Relation(
                                    residual,
                                    FormulaRelationOperator.GreaterThanOrEqual,
                                    Num(1))),
                            Equal(Multiply(binaryScale, binaryInfDist), oneThird),
                            Equal(
                                binaryInfDist,
                                new Formula.Fraction(
                                    Num(1),
                                    Multiply(Num(3), binaryScale))))))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every positive level, one declaration packages the source "
                                + "proposition's coprimality, pointwise numerator, nonzero "
                                + "residue, exact residual minimum, normalized distance, and "
                                + "unscaled distance clauses.")),
                        Paragraph(Text(
                            "The proof applies the pinned coprime-two characterization and each "
                                + "preceding public declaration. The radix-grid set itself is the "
                                + "frozen radixGrid definition imported from ConstantArms."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/ConstantArms")),
            ]));
    }
}
