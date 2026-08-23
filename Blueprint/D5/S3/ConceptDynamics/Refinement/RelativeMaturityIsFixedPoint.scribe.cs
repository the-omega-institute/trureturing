using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class RelativeMaturityIsFixedPointDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Refinement/RelativeMaturityIsFixedPoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A concept is mature relative to a question family exactly when every question in "
            + "the family already factors through it, and this maturity is not absolute.",
        H("Relative Maturity as a Fixed-Point Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("relative-maturity-is-family-wide-answerability"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "mature_iff_all_questions_answerable"),
                H("Relative maturity is exactly family-wide answerability"),
                StatementSource.FromAuthor(MaturityCriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A concept is mature for a family precisely when every question readout "
                            + "in that family factors through the concept. Equivalently, adjoining "
                            + "any one of those questions to the concept creates no distinction "
                            + "that the concept itself cannot already recover.")),
                    Paragraph(Text(
                        "For the forward direction, project a joint completion to its question "
                            + "coordinate and compose that projection with the maturity collapse. "
                            + "Conversely, the identity factorization of the concept together with "
                            + "the assumed factorization of each question invokes the universal "
                            + "property of the concept join."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("relative-maturity-depends-on-the-question-family"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "relative_maturity_is_not_absolute"),
                H("Maturity depends on the question family"),
                StatementSource.FromAuthor(RelativityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take the first Boolean coordinate as the concept. The constant "
                            + "Unit-indexed family that asks for that same first coordinate factors "
                            + "through the concept by the identity map, so the concept is mature "
                            + "for this family.")),
                    Paragraph(Text(
                        "The corresponding family that asks for the second coordinate does not "
                            + "factor through the first: the states (false, false) and "
                            + "(false, true) have the same first coordinate but different second "
                            + "coordinates. Thus one fixed concept is mature for one family and "
                            + "not mature for another."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Product(Formula first, Formula second) =>
        Seq(first, Sp, Times, Sp, second);

    private static Formula MatureFor(Formula concept, Formula questions) =>
        Call("MatureFor", concept, questions);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula MaturityCriterionFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula conceptType = F.Id("C");
        Formula valueType = F.Id("V");
        Formula concept = F.Id("qC");
        Formula questions = F.Id("questions");
        Formula index = F.Id("n");
        Formula everyQuestionFactors = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            indexType,
            Refines(Apply(questions, index), concept));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", F.Id("Type")),
                Bound("X", F.Id("Type")),
                Bound("C", F.Id("Type")),
                Bound("V", F.Id("Type")),
                Bound("qC", Arrow(stateType, conceptType)),
                Bound("questions", Arrow(indexType, Arrow(stateType, valueType))),
            ],
            new Formula.Logic(
                MatureFor(concept, questions),
                FormulaLogicOperator.Iff,
                everyQuestionFactors)));
    }

    private static Formula RelativityFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula stateType = Product(boolean, boolean);
        Formula concept = F.Id("qC");
        Formula questions = F.Id("questions");
        Formula otherQuestions = F.Id("otherQuestions");
        Formula conceptReadout = Arrow(stateType, boolean);
        Formula questionFamily = Arrow(unit, conceptReadout);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("qC", conceptReadout),
                Bound("questions", questionFamily),
                Bound("otherQuestions", questionFamily),
            ],
            new Formula.Logic(
                MatureFor(concept, questions),
                FormulaLogicOperator.And,
                new Formula.Not(MatureFor(concept, otherQuestions)))));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
