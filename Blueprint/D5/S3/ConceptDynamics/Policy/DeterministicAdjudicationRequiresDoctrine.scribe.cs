using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Policy;

internal sealed class DeterministicAdjudicationRequiresDoctrineDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Policy/DeterministicAdjudicationRequiresDoctrine.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two distinct licensed outcomes require a distinguishing doctrine input beyond "
            + "their common public-law value.",
        H("Deterministic Adjudication Requires Additional Doctrine"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adjudication-doctrine"),
                DeclarationHandle.Create(DeclarationPrefix + "AdjudicationDoctrine"),
                H("Additional adjudication doctrine"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier records exactly the six source alternatives: priority, "
                        + "equity, a historical anchor, value weights, a randomized "
                        + "selection, or a finer fact concept."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create(
                    "deterministic-adjudication-requires-additional-doctrine"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "deterministic_adjudication_requires_additional_doctrine"),
                H("Distinct licensed outcomes require additional doctrine"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The permitted-outcome predicate is built directly from "
                            + "admissibility, the public-law readout, and the permission "
                            + "relation. Two distinct witnesses rule out a unique outcome.")),
                    Paragraph(Text(
                        "A right-unique relation on the public-law value alone cannot "
                            + "realize both witnesses. After the doctrine channel is added, "
                            + "right uniqueness forces the two doctrine inputs to differ."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Apply(Formula function, Formula first, Formula second) =>
        new Formula.Apply(function, [first, second]);

    private static Formula Pair(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);

    private static Formula TheoremFormula()
    {
        Formula caseType = F.Id("Case");
        Formula factType = F.Id("PublicFact");
        Formula outcomeType = F.Id("Outcome");
        Formula weightType = F.Id("Weight");
        Formula seedType = F.Id("Seed");
        Formula fineFactType = F.Id("FineFact");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula prop = Seq(Operatorname, Grp(F.Id("Prop")));
        Formula publicLaw = F.Id("publicLaw");
        Formula admissible = F.Id("admissible");
        Formula permitted = F.Id("permitted");
        Formula fact = F.Id("b");
        Formula left = F.Id("y0");
        Formula right = F.Id("y1");
        Formula witness = F.Id("x");
        Formula chosen = F.Id("y");
        Formula publicAdjudicator = F.Id("publicAdjudicator");
        Formula adjudicator = F.Id("adjudicator");
        Formula leftDoctrine = F.Id("d0");
        Formula rightDoctrine = F.Id("d1");
        Formula doctrine = Call(
            "AdjudicationDoctrine",
            caseType,
            outcomeType,
            weightType,
            seedType,
            fineFactType);

        Formula Allowed(Formula x, Formula y) => Seq(
            Apply(admissible, x), Sp, Land, Sp,
            Equal(Apply(publicLaw, x), fact), Sp, Land, Sp,
            Apply(permitted, x, y));

        Formula ExistsAllowed(Formula x, Formula y) => Seq(
            Exists, Sp, x, Colon, Sp, caseType, Comma, Sp, Allowed(x, y));

        Formula multipleOutcomes = Seq(
            left, Sp, Neq, Sp, right, Sp, Land, Sp,
            Open, ExistsAllowed(F.Id("x0"), left), Close, Sp, Land, Sp,
            Open, ExistsAllowed(F.Id("x1"), right), Close);
        Formula uniqueOutcome = Seq(
            Exists, Sp, Bang, Sp, chosen, Colon, Sp, outcomeType, Comma, Sp,
            ExistsAllowed(witness, chosen));
        Formula publicAdjudicatorType = Arrow(
            factType,
            Arrow(outcomeType, prop));
        Formula noPublicAdjudicator = Seq(
            Neg, Open,
            Exists, Sp, publicAdjudicator, Colon, Sp, publicAdjudicatorType,
            Comma, Sp,
            Call("RightUnique", publicAdjudicator), Sp, Land, Sp,
            Apply(publicAdjudicator, fact, left), Sp, Land, Sp,
            Apply(publicAdjudicator, fact, right),
            Close);
        Formula adjudicatorType = Arrow(
            Seq(factType, Sp, Times, Sp, doctrine),
            Arrow(outcomeType, prop));
        Formula distinctDoctrine = Seq(
            Forall, Sp, adjudicator, Colon, Sp, adjudicatorType, Comma, Sp,
            Call("RightUnique", adjudicator), Sp, Rightarrow, Sp,
            Forall, Sp, leftDoctrine, Comma, Sp, rightDoctrine, Colon, Sp,
            doctrine, Comma, Sp,
            Open,
            Apply(adjudicator, Pair(fact, leftDoctrine), left), Sp, Land, Sp,
            Apply(adjudicator, Pair(fact, rightDoctrine), right),
            Close, Sp, Rightarrow, Sp,
            leftDoctrine, Sp, Neq, Sp, rightDoctrine);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, caseType, Comma, Sp, factType, Comma, Sp,
                outcomeType, Comma, Sp, weightType, Comma, Sp, seedType,
                Comma, Sp, fineFactType, Colon, Sp, type, Comma),
            Seq(
                publicLaw, Colon, Sp, Arrow(caseType, factType), Comma, Sp,
                admissible, Colon, Sp, Arrow(caseType, prop), Comma),
            Seq(
                permitted, Colon, Sp, Arrow(caseType, Arrow(outcomeType, prop)),
                Comma, Sp, fact, Colon, Sp, factType, Comma),
            Seq(
                left, Comma, Sp, right, Colon, Sp, outcomeType, Comma),
            Seq(Open, multipleOutcomes, Close, Sp, Rightarrow),
            Seq(
                Open,
                Neg, Open, uniqueOutcome, Close, Sp, Land, Sp,
                noPublicAdjudicator, Sp, Land, Sp,
                Open, distinctDoctrine, Close,
                Close, Dot),
        ]));
    }
}
