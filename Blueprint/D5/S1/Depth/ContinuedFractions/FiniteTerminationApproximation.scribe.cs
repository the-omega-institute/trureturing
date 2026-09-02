using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class FiniteTerminationApproximationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var q = Id("q");
        var Q = Id("Q");
        var x = Id("x");
        var naturals = Id("N");
        var rationals = Id("Q");
        var reals = Id("R");
        var zero = Num(0);
        var one = Num(1);

        Formula IntegerError(Formula denominator, Formula point) =>
            Call("integerApproximationError", denominator, point);

        Formula FiniteError(Formula level, Formula point) =>
            Call("finiteApproximationError", level, point);

        Formula Positive(Formula value) =>
            new Formula.Relation(zero, FormulaRelationOperator.LessThan, value);

        Formula Lambda(Formula binder, Formula body) =>
            F.Seq(F.Open, binder, F.Sp, F.Mapsto, F.Sp, body, F.Close);

        var product = Multiply(q, x);
        var integerErrorDefinition = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("q"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), reals),
            ],
            Equal(
                IntegerError(q, x),
                new Formula.Norm(Subtract(product, Call("round", product)))));

        var positiveDenominators = Call("Icc", one, Q);
        var finiteMinimum = Call(
            "min",
            new Formula.SetBuilder(IntegerError(q, x), q, positiveDenominators));
        var finiteErrorDefinition = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("Q"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("x"), reals),
            ],
            Equal(
                FiniteError(Q, x),
                Call("if", Positive(Q), finiteMinimum, zero)));

        var finiteTermination = new Formula.Logic(
            new Formula.Relation(x, FormulaRelationOperator.MemberOf, rationals),
            FormulaLogicOperator.Iff,
            new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("Q"),
                naturals,
                new Formula.Logic(
                    Positive(Q),
                    FormulaLogicOperator.And,
                    Equal(FiniteError(Q, x), zero))));
        var noFiniteTermination = new Formula.Logic(
            Call("Irrational", x),
            FormulaLogicOperator.Implies,
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("Q"),
                naturals,
                new Formula.Logic(
                    Positive(Q),
                    FormulaLogicOperator.Implies,
                    Positive(FiniteError(Q, x)))));
        var infiniteApproximation = Equal(
            Call("liminfAtTop", Lambda(Q, FiniteError(Q, x))),
            zero);
        var theoremStatement = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            reals,
            new Formula.Logic(
                finiteTermination,
                FormulaLogicOperator.And,
                new Formula.Logic(
                    noFiniteTermination,
                    FormulaLogicOperator.And,
                    infiniteApproximation)));

        const string declarationPrefix =
            "D5/S1/Depth/ContinuedFractions/FiniteTerminationApproximation.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Rational reals terminate at a finite denominator; irrational errors stay positive "
                + "at every finite level while their liminf is zero.",
            H("Finite Termination and Infinite Approximation"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("nearest-integer-approximation-error"),
                    DeclarationHandle.Create(declarationPrefix + "integerApproximationError"),
                    H("Nearest-integer approximation error"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(integerErrorDefinition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For a natural denominator q and real point x, this is the absolute "
                            + "distance from q times x to its nearest integer."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("finite-approximation-error"),
                    DeclarationHandle.Create(declarationPrefix + "finiteApproximationError"),
                    H("Finite approximation error"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(finiteErrorDefinition)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "At a positive level Q this is the finite minimum over denominators from "
                            + "one through Q. The zero branch only totalizes the function at the "
                            + "single level excluded by the source minimum."))),
                    DescribeRole.Definition),
                Describe.Lean(
                    DescribeId.Create("finite-termination-and-infinite-approximation"),
                    DeclarationHandle.Create(
                        declarationPrefix + "finite_termination_and_infinite_approximation"),
                    H("Finite termination and infinite approximation"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(theoremStatement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "A rational denominator makes one finite error exactly zero. "
                                + "Conversely, a zero error writes the real as an integer divided "
                                + "by a positive natural denominator.")),
                        Paragraph(Text(
                            "For an irrational real, every candidate nearest-integer error is "
                                + "nonzero, so its attained finite minimum is strictly positive.")),
                        Paragraph(Text(
                            "Dirichlet approximation bounds the level-Q minimum by one over Q "
                                + "plus one. Squeezing against nonnegativity proves convergence to "
                                + "zero for every real, which is stronger than the irrational-only "
                                + "liminf clause."))),
                    DescribeRole.Theorem))));
    }
}
