using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.DBonacciGeneral;

internal sealed class TribonacciPeriodicGeneratorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var gap = Id("g");
        var period = Id("p");
        var state = Id("s");
        var code = Id("c");
        var gaps = Id("TribonacciGap");
        var naturals = Id("N");
        var states = Id("TribonacciPeriodicState");
        var codes = Id("TribonacciCubicCode");

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        var branchCompatibility = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("g"),
            gaps,
            Equal(
                Call("mapTargets", Call("tribonacciStepsFrom", gap)),
                Call("gapLetterSubstitution", gap)));

        var periodic = Equal(
            Call("iterate", Id("tribonacciPeriodicTransition"), period, state),
            state);
        var denominatorNonzero = NotEqual(
            Call("fixedPointDenominator", period, state),
            Num(0));
        var generatedCode = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("c"),
            codes,
            new Formula.Logic(
                Member(code, Call("tribonacciFixedPointCodes", period)),
                FormulaLogicOperator.And,
                Equal(state, Call("decodeTribonacciState", code))));
        var complete = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                new Formula.BoundVariable(FormulaIdentifier.Create("p"), naturals),
                new Formula.BoundVariable(FormulaIdentifier.Create("s"), states),
            ],
            new Formula.Logic(
                new Formula.Logic(
                    periodic,
                    FormulaLogicOperator.And,
                    denominatorNonzero),
                FormulaLogicOperator.Implies,
                generatedCode));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Five certified branches and exact cubic arithmetic generate every periodic fixed-point equation.",
            H("Tribonacci Periodic Generator"),
            Blocks(
                Paragraph(Text(
                    "The three normalized gap types have one, two, and two legal outgoing "
                        + "branches. Affine compositions are evaluated exactly in Q(t), using "
                        + "t cubed equal to t squared plus t plus one.")),
                Describe.Lean(
                    DescribeId.Create("branch-targets-match-the-gap-substitution"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator."
                            + "tribonacci_steps_from_targets"),
                    H("Branch targets match the frozen substitution"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(branchCompatibility)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Mapping each legal edge to its target gap gives exactly the frozen "
                            + "three-letter Tribonacci gap substitution."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("periodic-points-return-to-generated-cubic-codes"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/DBonacciGeneral/TribonacciPeriodicGenerator."
                            + "tribonacci_periodic_point_enumeration_complete"),
                    H("Periodic points return to generated cubic codes"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(complete)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "Reading the actual legal branch at every iterate constructs a closed "
                            + "symbolic word. When its exact fixed-point denominator is nonzero, "
                            + "the original real state is the decoding of the generated code."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/DBonacci/OrbitAlgebra")),
            ]));
    }
}
