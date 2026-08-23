using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Answering;

internal sealed class InformationRefinementShrinksAnswersDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Answering/InformationRefinementShrinksAnswers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Information refinement can only shrink the set of possible answers, can do so "
            + "strictly, and is ruled out by the appearance of a new answer.",
        H("Information Refinement Shrinks Answers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("information-refinement-cannot-enlarge-possible-answers"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "answer_set_antitone_in_information"),
                H("Information refinement cannot enlarge possible answers"),
                StatementSource.FromAuthor(AntitoneAnswerSetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A possible answer is the image under T of at least one world that "
                            + "remains compatible with the available information. If every "
                            + "world in the refined set R already belongs to S, the same world "
                            + "witnesses that answer before refinement.")),
                    Paragraph(Text(
                        "Thus removing possible worlds cannot create an answer outside the "
                            + "former image. The answer-set construction is covariant in sets "
                            + "of worlds, which makes it antitone when greater information is "
                            + "represented by a smaller set of possibilities."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("boolean-refinement-shrinks-answers-strictly"),
                DeclarationHandle.Create(DeclarationPrefix + "strict_refinement_witness"),
                H("Boolean refinement shrinks possible answers strictly"),
                StatementSource.FromAuthor(StrictRefinementWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under complete ignorance, both Boolean worlds remain possible and the "
                            + "identity readout can return either truth value. Learning that the "
                            + "world is true leaves only the singleton containing true.")),
                    Paragraph(Text(
                        "The refinement is proper because it excludes false, and its answer "
                            + "image is proper for the same reason: false was formerly possible "
                            + "as an answer but is no longer attained."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("answer-growth-rules-out-information-refinement"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "answer_growth_precludes_refinement"),
                H("Answer growth rules out information refinement"),
                StatementSource.FromAuthor(AnswerGrowthPrecludesRefinementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Suppose the new possible-world set admits an answer that the old set "
                            + "did not. The new set cannot have been obtained solely by removing "
                            + "old possibilities.")),
                    Paragraph(Text(
                        "Indeed, containment of the new worlds in the old worlds would invoke "
                            + "answer-set antitonicity and contain the new answer image in the "
                            + "old one, contradicting the observed answer growth."))),
                DescribeRole.Lemma))));

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula SetOf(Formula carrier) =>
        Call("Set", carrier);

    private static Formula Ans(Formula target, Formula worlds) =>
        Call("Ans", target, worlds);

    private static Formula Universe(Formula carrier) =>
        Call("univ", carrier);

    private static Formula SubsetOf(Formula subset, Formula superset) =>
        new Formula.Relation(subset, FormulaRelationOperator.SubsetOf, superset);

    private static Formula StrictSubsetOf(Formula subset, Formula superset) =>
        Seq(subset, Sp, Subset, Sp, superset);

    private static Formula ImpliesFormula(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula AntitoneAnswerSetFormula()
    {
        Formula world = F.Id("World");
        Formula answer = F.Id("Answer");
        Formula target = F.Id("T");
        Formula refined = F.Id("R");
        Formula original = F.Id("S");
        Formula worldSet = SetOf(world);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("World", TypeUniverse()),
                Bound("Answer", TypeUniverse()),
                Bound("T", Arrow(world, answer)),
                Bound("R", worldSet),
                Bound("S", worldSet),
            ],
            ImpliesFormula(
                SubsetOf(refined, original),
                SubsetOf(Ans(target, refined), Ans(target, original)))));
    }

    private static Formula StrictRefinementWitnessFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula singletonTrue = new Formula.SetLiteral([F.Id("true")]);
        Formula allBooleans = Universe(boolean);
        Formula identity = F.Id("id");

        return Disp(And(
            StrictSubsetOf(singletonTrue, allBooleans),
            StrictSubsetOf(
                Ans(identity, singletonTrue),
                Ans(identity, allBooleans))));
    }

    private static Formula AnswerGrowthPrecludesRefinementFormula()
    {
        Formula world = F.Id("World");
        Formula answer = F.Id("Answer");
        Formula target = F.Id("T");
        Formula refined = F.Id("R");
        Formula original = F.Id("S");
        Formula worldSet = SetOf(world);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("World", TypeUniverse()),
                Bound("Answer", TypeUniverse()),
                Bound("T", Arrow(world, answer)),
                Bound("R", worldSet),
                Bound("S", worldSet),
            ],
            ImpliesFormula(
                new Formula.Not(SubsetOf(Ans(target, refined), Ans(target, original))),
                new Formula.Not(SubsetOf(refined, original)))));
    }
}
