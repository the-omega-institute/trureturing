using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.TribonacciSurvivors;

internal sealed class StrictFiniteDepthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var n = Id("n");
        var state = Id("s");
        var naturals = Id("N");
        var states = Id("TribonacciPeriodicState");
        var strictSet = Id("tribonacciStrictSurvivorSet");

        Formula Backward(Formula depth) =>
            Call("tribonacciBackwardSurvivor", strictSet, depth);

        Formula Member(Formula value, Formula set) =>
            new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);

        Formula NonemptyAt(Formula depth) => new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("s"),
            states,
            Member(state, Backward(depth)));

        var everyDepth = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            naturals,
            NonemptyAt(n));

        var depthSixty = NonemptyAt(Num(60));

        var separation = new Formula.Logic(
            everyDepth,
            FormulaLogicOperator.And,
            Equal(Id("tribonacciStrictPermanentSet"), Id("emptySet")));

        const string declarationPrefix =
            "D5/S0/Tower/TribonacciSurvivors/StrictFiniteDepth.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "Every finite strict Tribonacci backward-survivor depth is nonempty, so the "
                + "strict forbidden region never becomes empty at a finite depth.",
            H("Strict Finite Depth"),
            Blocks(
                Paragraph(Text(
                    "The threshold period-two orbit sits exactly on the strict boundary: its "
                        + "large phase has arm exactly equal to the threshold. Perturbing the "
                        + "large coordinate downward by a budget that the expanding map has not "
                        + "yet inflated past the middle slack keeps every visited arm strictly "
                        + "above the threshold. Choosing the perturbation proportional to a "
                        + "negative power of the Tribonacci constant therefore realizes any "
                        + "prescribed finite depth.")),
                Describe.Lean(
                    DescribeId.Create("tribonacci-strict-finite-depth-is-nonempty"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_strict_backward_survivor_nonempty"),
                    H("Every finite strict depth is nonempty"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(everyDepth)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The witness is the large champion coordinate reduced by half the "
                            + "middle slack divided by the depth-th power of the Tribonacci "
                            + "constant. The bound is strict at every visited state, so the "
                            + "membership is not a boundary artifact."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-strict-depth-sixty-is-nonempty"),
                    DeclarationHandle.Create(
                        declarationPrefix + "tribonacci_strict_backward_survivor_sixty_nonempty"),
                    H("Depth sixty is nonempty"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(depthSixty)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "This is the direct refutation of the announced emptiness at depth "
                            + "sixty. Interval iteration in one hundred forty decimal digits "
                            + "independently measures the depth-sixty level at about nine times "
                            + "ten to the minus seventeen, and the level is still positive at "
                            + "depth one hundred twenty."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("tribonacci-finite-depths-versus-permanent-set"),
                    DeclarationHandle.Create(
                        declarationPrefix
                            + "tribonacci_finite_depths_nonempty_and_permanent_empty"),
                    H("Finite depths and the permanent set separate"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(separation)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The levels are open sets, so a nested intersection may be empty while "
                            + "every level is nonempty. Emptiness of the all-depth intersection "
                            + "therefore decides no finite level, and the two statements are "
                            + "consistent."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/TribonacciSurvivors/TribonacciPermanentSurvivors")),
            ]));
    }
}
