using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Axis;

internal sealed class AxisWeightDegeneracyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var x = Id("x");
        var y = Id("y");
        var reals = Id("R");

        var locus = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("y"), reals),
            ],
            new Formula.Logic(
                Equal(Call("axisWeight", x, y, Num(0)), Call("axisWeight", x, y, Num(1))),
                FormulaLogicOperator.Iff,
                Equal(x, y)));

        var witness = Equal(
            Call("axisWeight", Num(1), Num(1), Num(0)),
            Call("axisWeight", Num(1), Num(1), Num(1)));

        var offDiagonal = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), reals),
                new Formula.BoundVariable(FormulaIdentifier.Create("y"), reals),
            ],
            new Formula.Logic(
                NotEqual(x, y),
                FormulaLogicOperator.Implies,
                NotEqual(
                    Call("axisWeight", x, y, Num(0)),
                    Call("axisWeight", x, y, Num(1)))));

        var quadratic = new Formula.Logic(
            Equal(Subtract(new Formula.Power(Id("phi"), Num(2)), Id("phi")), Num(1)),
            FormulaLogicOperator.And,
            Equal(Subtract(new Formula.Power(Id("psi"), Num(2)), Id("psi")), Num(1)));

        var statement = new Formula.Logic(
            locus,
            FormulaLogicOperator.And,
            new Formula.Logic(witness, FormulaLogicOperator.And, offDiagonal));

        const string declarationPrefix = "D5/S3/Axis/AxisWeightDegeneracy.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Consecutive axis weights coincide exactly on the diagonal of the two readings.",
            H("Axis Weight Degeneracy"),
            Blocks(
                Paragraph(Text(
                    "The axis weight reads a pair of parameters at the two Galois embeddings "
                        + "and raises each to the depth. Both the golden ratio and its "
                        + "conjugate satisfy the same quadratic, so each drops its square by "
                        + "exactly one unit of itself, and the first step of the tower "
                        + "compares the two readings against each other and nothing else.")),
                Paragraph(Text(
                    "The consequence is that depth zero and depth one carry the same weight "
                        + "precisely when the two readings agree. The locus is a line, not a "
                        + "point, and it contains readings that are in no sense degenerate.")),
                Paragraph(Text(
                    "This module exists as an erratum. The prose attached to the depth-zero "
                        + "evaluation in the trace recurrence asserts that consecutive depths "
                        + "never carry the same weight except under a trivial reading. That "
                        + "assertion is not proved by the theorem it is attached to, and it is "
                        + "false. The frozen module is left byte-identical; the correction is "
                        + "carried here as a stronger statement naming the exact locus, so the "
                        + "false sentence is closed by a truth rather than by a deletion.")),
                Describe.Lean(
                    DescribeId.Create("both-embeddings-drop-their-square-by-one-unit"),
                    DeclarationHandle.Create(declarationPrefix + "sq_sub_self"),
                    H("Both embeddings drop their square by one unit"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(quadratic)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Each of the two roots of the golden quadratic satisfies the same "
                            + "identity, which is the single fact the degeneracy computation "
                            + "needs at both embeddings."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-first-weight-step-degenerates-exactly-on-the-diagonal"),
                    DeclarationHandle.Create(
                        declarationPrefix + "axisWeight_zero_eq_one_iff"),
                    H("The first weight step degenerates exactly on the diagonal"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(locus)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Cancelling the exponential and substituting the quadratic on both "
                            + "embeddings leaves the difference of the two readings, so the "
                            + "weights agree if and only if those readings agree."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("degeneracy-occurs-away-from-any-trivial-reading"),
                    DeclarationHandle.Create(
                        declarationPrefix + "degeneracy_occurs_off_the_trivial_reading"),
                    H("Degeneracy occurs away from any trivial reading"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(witness)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Taking both readings equal to one exhibits a coincidence of "
                            + "consecutive weights at a reading that is not trivial, which is "
                            + "the counterexample the erratum carries."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("off-the-diagonal-consecutive-weights-differ"),
                    DeclarationHandle.Create(
                        declarationPrefix + "axisWeight_zero_ne_one_off_diagonal"),
                    H("Off the diagonal consecutive weights differ"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(offDiagonal)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The coincidence is confined to the diagonal: whenever the two "
                            + "readings differ, so do the weights at the first two depths."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("the-degeneracy-locus-packaged"),
                    DeclarationHandle.Create(
                        declarationPrefix + "axis_weight_degeneracy_locus_package"),
                    H("The degeneracy locus packaged"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "One conjunction carrying the correction: degeneracy holds exactly on "
                            + "the diagonal, it is attained at a nontrivial reading, and it "
                            + "fails everywhere off that line."))),
                    DescribeRole.Theorem))));
    }
}
