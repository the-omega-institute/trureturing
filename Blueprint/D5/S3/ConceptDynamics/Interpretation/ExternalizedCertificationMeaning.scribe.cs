using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interpretation;

internal sealed class ExternalizedCertificationMeaningDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One realized decision transcript can carry collapsed or independently sampled "
            + "certification value.",
        H("Externalized Certification Meaning"),
        Blocks(Describe.Lean(
            DescribeId.Create("externalized-certification-meaning"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Interpretation/ExternalizedCertificationMeaning."
                    + "externalized_certification_meaning"),
            H("Certification meaning is external to the decision transcript"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The implementation is the constant-false Boolean program and the expected "
                        + "behavior is the identity. The constructed deployment law gives the "
                        + "single failing input mass (1 + epsilon)/2, strictly above epsilon.")),
                Paragraph(Text(
                    "Both worlds realize the same all-false suite and therefore the same "
                        + "all-green bit transcript. In the co-selected world every coordinate "
                        + "law is concentrated on that realized input. In the independent world "
                        + "every coordinate law equals the deployment law.")),
                Paragraph(Text(
                    "The bad-green mass is the product of the coordinate pass masses. It is one "
                        + "under co-selection and ((1 - epsilon)/2)^m under independent sampling. "
                        + "The repository exponential bound gives the displayed certification "
                        + "envelope, while positivity of epsilon and m makes the co-selected mass "
                        + "strictly exceed that envelope.")),
                Paragraph(Text(
                    "The final two clauses state the information-theoretic corollary directly: "
                        + "neither bad-green mass nor the independent-sampling precondition factors "
                        + "through the transcript. The source explicitly leaves signature semantics "
                        + "out of scope, so no separate universal semantics of signing is invented."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Field(Formula value, byte field) =>
        Seq(value, Dot, D(field));

    private static Formula ToReal(Formula value) =>
        Seq(Open, value, Close, Dot, F.Id("toReal"));

    private static Formula TheoremFormula()
    {
        Formula epsilon = F.Id("epsilon");
        Formula budget = F.Id("m");
        Formula deployment = Mu;
        Formula coSelected = new Formula.Subscript(F.Id("W"), F.Id("c"));
        Formula independent = new Formula.Subscript(F.Id("W"), F.Id("i"));
        Formula index = F.Id("j");
        Formula input = F.Id("input");
        Formula worldValue = F.Id("world");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula boolType = F.Id("Bool");
        Formula pmfBool = Call("PMF", boolType);
        Formula finBudget = Call("Fin", budget);
        Formula implementation = F.Id("implementation");
        Formula expected = F.Id("expected");
        Formula world = F.Id("World");
        Formula transcript = F.Id("transcript");
        Formula badGreen = F.Id("badGreenMass");
        Formula worldType = Seq(
            Open, Arrow(finBudget, pmfBool), Close, Sp, Times, Sp,
            Open, Arrow(finBudget, boolType), Close);
        Formula worldSuite = Field(worldValue, 2);
        Formula worldLaws = Field(worldValue, 1);
        Formula realizedInput = Apply(worldSuite, index);
        Formula implementationDefinition = Seq(
            implementation, Colon, Sp, Arrow(boolType, boolType), Sp, Eq, Sp,
            Open, Underscore, Sp, Mapsto, Sp, F.Id("false"), Close);
        Formula expectedDefinition = Seq(
            expected, Colon, Sp, Arrow(boolType, boolType), Sp, Eq, Sp, F.Id("id"));
        Formula worldDefinition = Seq(world, Sp, Eq, Sp, worldType);
        Formula transcriptDefinition = Seq(
            transcript, Colon, Sp, Arrow(world, Arrow(finBudget, boolType)), Sp, Eq, Sp,
            Open, worldValue, Sp, Mapsto, Sp, index, Sp, Mapsto, Sp,
            Call("decide", Seq(
                Apply(implementation, realizedInput), Sp, Eq, Sp,
                Apply(expected, realizedInput))), Close);
        Formula badGreenDefinition = Seq(
            badGreen, Colon, Sp, Arrow(world, real), Sp, Eq, Sp,
            Open, worldValue, Sp, Mapsto, Sp,
            Prod, Underscore, Grp(index), Sp,
            ToReal(Apply(Apply(worldLaws, index), F.Id("false"))), Close);
        Formula suiteCo = Field(coSelected, 2);
        Formula suiteIndependent = Field(independent, 2);
        Formula lawsCo = Field(coSelected, 1);
        Formula lawsIndependent = Field(independent, 1);
        Formula loss = Seq(
            Sum, Underscore, Grp(input, Colon, Sp, boolType), Sp,
            F.Text, Grp(F.Id("if"), Sp),
            Apply(implementation, input), Sp, Eq, Sp, Apply(expected, input),
            F.Text, Grp(Sp, F.Id("then"), Sp), D(0),
            F.Text, Grp(Sp, F.Id("else"), Sp),
            ToReal(Apply(deployment, input)));
        Formula independentRate = new Formula.Fraction(
            Seq(D(1), Minus, epsilon), D(2));
        Formula independentMass = new Formula.Power(
            Seq(independentRate), Seq(budget));
        Formula envelope = Call(
            "exp", Seq(Minus, Open, epsilon, Sp, Times, Sp,
                Open, budget, Colon, Sp, real, Close, Close));
        Formula factorsMass = Call("FactorsThrough", badGreen, transcript);
        Formula independentPredicate = Seq(
            Open, worldValue, Sp, Mapsto, Sp,
            Forall, Sp, index, Comma, Sp,
            Apply(Field(worldValue, 1), index), Sp, Eq, Sp, deployment, Close);
        Formula factorsIndependence =
            Call("FactorsThrough", independentPredicate, transcript);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, epsilon, Colon, Sp, real, Comma, Sp,
            budget, Colon, Sp, natural, Comma, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, epsilon, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, budget, Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            implementationDefinition, Comma, RowBreak, Grp(),
            expectedDefinition, Comma, RowBreak, Grp(),
            worldDefinition, Comma, RowBreak, Grp(),
            transcriptDefinition, Comma, RowBreak, Grp(),
            badGreenDefinition, Close, Semi, RowBreak, Grp(),
            Exists, Sp, deployment, Colon, Sp, pmfBool, Comma, Sp,
            coSelected, Comma, Sp, independent, Colon, Sp, world, Comma,
            RowBreak, Grp(),
            suiteCo, Sp, Eq, Sp, suiteIndependent, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            Apply(suiteCo, index), Sp, Eq, Sp, F.Id("false"), Close, Sp, Land,
            RowBreak, Grp(),
            Apply(transcript, coSelected), Sp, Eq, Sp,
            Apply(transcript, independent), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            Apply(lawsCo, index), Sp, Eq, Sp,
            Call("pure", Apply(suiteCo, index)), Close, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            Apply(lawsIndependent, index), Sp, Eq, Sp,
            deployment, Close, Sp, Land, RowBreak, Grp(),
            loss, Sp, Eq, Sp,
            new Formula.Fraction(Seq(D(1), Plus, epsilon), D(2)), Sp, Land,
            RowBreak, Grp(),
            epsilon, Sp, Lt, Sp, loss, Sp, Land, RowBreak, Grp(),
            Apply(badGreen, coSelected), Sp, Eq, Sp, D(1), Sp, Land,
            RowBreak, Grp(),
            Apply(badGreen, independent), Sp, Eq, Sp,
            independentMass, Sp, Land, RowBreak, Grp(),
            Apply(badGreen, independent), Sp, Leq, Sp,
            envelope, Sp, Land, RowBreak, Grp(),
            envelope, Sp, Lt, Sp, Apply(badGreen, coSelected), Sp, Land,
            RowBreak, Grp(),
            lawsCo, Sp, Neq, Sp, lawsIndependent, Sp, Land, RowBreak, Grp(),
            Neg, Sp, factorsMass, Sp, Land, RowBreak, Grp(),
            Neg, Sp, factorsIndependence, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
