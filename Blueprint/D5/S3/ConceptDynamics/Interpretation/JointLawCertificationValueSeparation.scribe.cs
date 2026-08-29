using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interpretation;

internal sealed class JointLawCertificationValueSeparationDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Interpretation/JointLawCertificationValueSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same complete decision transcript can carry separated certification values under "
            + "co-selected and independently sampled joint laws.",
        H("Joint-Law Certification Value Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("joint-law-certification-value-separation"),
            DeclarationHandle.Create(
                DeclarationPrefix + "joint_law_certification_value_separation"),
            H("Certification value is not a function of the decision transcript"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a threshold strictly between zero and one and a positive suite budget, "
                        + "the implementation is the constant-false Boolean program and the "
                        + "expected behavior is the identity.")),
                Paragraph(Text(
                    "The two worlds realize the same suite and the same complete suite-and-verdict "
                        + "transcript. The co-selected world has the Dirac law at that suite, while "
                        + "the independent world has the finite product of the deployment law.")),
                Paragraph(Text(
                    "Deployment loss is strictly above epsilon. The co-selected bad-green mass is "
                        + "one, while the independent mass is the displayed product and lies below "
                        + "the exponential envelope; positive budget makes the separation strict.")),
                Paragraph(Text(
                    "The final clauses state directly that neither certification value nor the "
                        + "independent-product-law status factors through the transcript."))),
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
        Formula worldValue = F.Id("world");
        Formula index = F.Id("j");
        Formula input = F.Id("input");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula boolType = F.Id("Bool");
        Formula pmfBool = Call("PMF", boolType);
        Formula finBudget = Call("Fin", budget);
        Formula suiteType = Arrow(finBudget, boolType);
        Formula measureSuite = Call("Measure", suiteType);
        Formula world = F.Id("World");
        Formula worldType = Seq(
            Open, measureSuite, Close, Sp, Times, Sp, Open, suiteType, Close);
        Formula implementation = F.Id("implementation");
        Formula expected = F.Id("expected");
        Formula transcript = F.Id("transcript");
        Formula certificationValue = F.Id("certificationValue");
        Formula worldSuite = Field(worldValue, 2);
        Formula worldLaw = Field(worldValue, 1);
        Formula realizedInput = Apply(worldSuite, index);
        Formula implementationDefinition = Seq(
            implementation, Colon, Sp, Arrow(boolType, boolType), Sp, Eq, Sp,
            Open, Underscore, Sp, Mapsto, Sp, F.Id("false"), Close);
        Formula expectedDefinition = Seq(
            expected, Colon, Sp, Arrow(boolType, boolType), Sp, Eq, Sp, F.Id("id"));
        Formula worldDefinition = Seq(world, Sp, Eq, Sp, worldType);
        Formula decisionBits = Seq(
            Open, index, Sp, Mapsto, Sp,
            Call("decide", Seq(
                Apply(implementation, realizedInput), Sp, Eq, Sp,
                Apply(expected, realizedInput))), Close);
        Formula transcriptType = Arrow(
            world,
            Seq(Open, suiteType, Close, Sp, Times, Sp, Open, suiteType, Close));
        Formula transcriptDefinition = Seq(
            transcript, Colon, Sp, transcriptType, Sp, Eq, Sp,
            Open, worldValue, Sp, Mapsto, Sp,
            Open, worldSuite, Comma, Sp, decisionBits, Close, Close);
        Formula certificationValueDefinition = Seq(
            certificationValue, Colon, Sp, Arrow(world, real), Sp, Eq, Sp,
            Open, worldValue, Sp, Mapsto, Sp,
            Call("badGreenMass", implementation, expected, worldLaw), Close);
        Formula suiteCo = Field(coSelected, 2);
        Formula suiteIndependent = Field(independent, 2);
        Formula lawCo = Field(coSelected, 1);
        Formula lawIndependent = Field(independent, 1);
        Formula productLaw = Call(
            "pi", Seq(index, Sp, Mapsto, Sp, Call("toMeasure", deployment)));
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
        Formula factorsValue = Call(
            "FactorsThrough", certificationValue, transcript);
        Formula independentPredicate = Seq(
            Open, worldValue, Sp, Mapsto, Sp,
            Field(worldValue, 1), Sp, Eq, Sp, productLaw, Close);
        Formula factorsIndependence = Call(
            "FactorsThrough", independentPredicate, transcript);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, epsilon, Colon, Sp, real, Comma, Sp,
            budget, Colon, Sp, natural, Comma, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, epsilon, Sp, Land, Sp,
            epsilon, Sp, Lt, Sp, D(1), Sp, Land, Sp,
            D(0), Sp, Lt, Sp, budget, Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            implementationDefinition, Comma, RowBreak, Grp(),
            expectedDefinition, Comma, RowBreak, Grp(),
            worldDefinition, Comma, RowBreak, Grp(),
            transcriptDefinition, Comma, RowBreak, Grp(),
            certificationValueDefinition, Close, Semi, RowBreak, Grp(),
            Exists, Sp, deployment, Colon, Sp, pmfBool, Comma, Sp,
            coSelected, Comma, Sp, independent, Colon, Sp, world, Comma,
            RowBreak, Grp(),
            suiteCo, Sp, Eq, Sp, suiteIndependent, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            Apply(suiteCo, index), Sp, Eq, Sp, F.Id("false"), Close,
            Sp, Land, RowBreak, Grp(),
            Apply(transcript, coSelected), Sp, Eq, Sp,
            Apply(transcript, independent), Sp, Land, RowBreak, Grp(),
            lawCo, Sp, Eq, Sp, Call("dirac", suiteCo),
            Sp, Land, RowBreak, Grp(),
            lawIndependent, Sp, Eq, Sp, productLaw,
            Sp, Land, RowBreak, Grp(),
            loss, Sp, Eq, Sp,
            new Formula.Fraction(Seq(D(1), Plus, epsilon), D(2)),
            Sp, Land, RowBreak, Grp(),
            epsilon, Sp, Lt, Sp, loss, Sp, Land, RowBreak, Grp(),
            Apply(certificationValue, coSelected), Sp, Eq, Sp, D(1),
            Sp, Land, RowBreak, Grp(),
            Apply(certificationValue, independent), Sp, Eq, Sp,
            independentMass, Sp, Land, RowBreak, Grp(),
            Apply(certificationValue, independent), Sp, Leq, Sp,
            envelope, Sp, Land, RowBreak, Grp(),
            envelope, Sp, Lt, Sp, Apply(certificationValue, coSelected),
            Sp, Land, RowBreak, Grp(),
            lawCo, Sp, Neq, Sp, lawIndependent,
            Sp, Land, RowBreak, Grp(),
            Neg, Sp, factorsValue, Sp, Land, RowBreak, Grp(),
            Neg, Sp, factorsIndependence, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
