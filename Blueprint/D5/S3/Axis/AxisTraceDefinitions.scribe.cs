using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class AxisTraceDefinitionsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var K = Id("K");
        var n = Id("n");

        var weight = Equal(
            Call("t", K),
            Call("exp",
                Subtract(
                    Multiply(Id("y"), new Formula.Power(Id("psi"), Add(K, Num(1)))),
                    Multiply(Id("x"), new Formula.Power(Id("phi"), Add(K, Num(1)))))));

        var sum = Equal(
            Call("W", K),
            Call("sum", Call("range", Call("fib", Add(K, Num(1)))), Call("wordWeight", n)));

        var bridge = new Formula.Logic(
            new Formula.Relation(
                Call("greatestFib", n), FormulaRelationOperator.LessThanOrEqual, K),
            FormulaLogicOperator.Iff,
            new Formula.Relation(n, FormulaRelationOperator.LessThan, Call("fib", Add(K, Num(1)))));

        const string declarationPrefix = "D5/S3/Axis/AxisTraceDefinitions.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The partial sum ranges over words of bounded depth; the weight is the exponential.",
            H("Axis Trace Definitions"),
            Blocks(
                Paragraph(Text(
                    "The clause introduces two objects: the axis weight at a depth, read as an "
                        + "exponential at the two Galois embeddings, and the axis partial sum, "
                        + "the total weight of the legal words whose digit depth is at most "
                        + "that depth.")),
                Paragraph(Text(
                    "The implementation sums over an initial segment of the naturals rather "
                        + "than over a set described by depth. Those are the same family only "
                        + "because depth at most K is exactly membership below the next "
                        + "Fibonacci number. That equivalence is the third conjunct here: "
                        + "without it the bound in the definition would be an unexplained "
                        + "constant, and a reader could not check the implementation against "
                        + "the source line.")),
                Describe.Lean(
                    DescribeId.Create("the-two-objects-and-the-depth-bridge"),
                    DeclarationHandle.Create(declarationPrefix + "axis_trace_definitions"),
                    H("The two objects and the depth bridge"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(
                        new Formula.Logic(
                            weight,
                            FormulaLogicOperator.And,
                            new Formula.Logic(sum, FormulaLogicOperator.And, bridge)))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The first two conjuncts hold by definition and pin it: changing the "
                            + "exponent or the summation bound makes the module fail to build. "
                            + "The third is a proved equivalence rather than a restatement, and "
                            + "it is what makes the summation bound mean bounded depth."))),
                    DescribeRole.Theorem))));
    }
}
