using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.NonPisotFrontier;

internal sealed class OrbitWitnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var w = Id("conjugateStep4");
        var root = Call("sqrt", Num(13));

        var closed = Equal(w, Add(Num(4), root));
        var passes = new Formula.Relation(
            Add(Num(3), root), FormulaRelationOperator.LessThan,
            new Formula.Absolute(w));

        var statement = new Formula.Logic(closed, FormulaLogicOperator.And, passes);

        const string declarationPrefix =
            "D5/S0/Tower/NonPisotFrontier/OrbitWitness.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "After four greedy steps the conjugate coordinate is four plus the square root of "
                + "thirteen, one beyond the escape threshold.",
            H("Orbit Witness"),
            Blocks(
                Paragraph(Text(
                    "The four digit bounds are wide, the tightest margin being about three "
                        + "tenths, so the two bounds on the square root of thirteen suffice and "
                        + "no numeric approximation of the base is needed. Each remainder is "
                        + "carried as an integer pair against one and the base, and the step is "
                        + "closed by the quadratic the base satisfies.")),
                Describe.Lean(
                    DescribeId.Create("the-fourth-conjugate-iterate-passes-the-threshold"),
                    DeclarationHandle.Create(
                        declarationPrefix + "first_four_digits_and_witness"),
                    H("The fourth conjugate iterate passes the threshold"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(statement)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The third iterate sits exactly on the threshold in absolute value and "
                            + "the fourth is exactly one beyond it, both as closed algebraic "
                            + "values rather than approximations."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/NonPisotFrontier/ConjugateBridge")),
            ]));
    }
}
