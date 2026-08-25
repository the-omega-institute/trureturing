using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Interpretation;

internal sealed class JointLawExternalizedCertificationMeaningDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Interpretation/JointLawExternalizedCertificationMeaning.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A realized suite does not determine whether its certification law was co-selected "
            + "or independently sampled.",
        H("Joint-Law Externalized Certification Meaning"),
        Blocks(Describe.Lean(
            DescribeId.Create("joint-law-externalized-certification-meaning"),
            DeclarationHandle.Create(
                DeclarationPrefix + "joint_law_externalized_certification_meaning"),
            H("Certification meaning is carried by a joint sampling law"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The implementation is the constant-false Boolean program and the expected "
                        + "behavior is the identity. A Boolean deployment PMF assigns the failing "
                        + "input mass (1 + epsilon)/2.")),
                Paragraph(Text(
                    "Both worlds realize the same all-false suite. The co-selected world uses the "
                        + "Dirac law at that suite, while the independently sampled world uses the "
                        + "finite product measure of copies of the deployment law.")),
                Paragraph(Text(
                    "These five independently falsifiable world clauses are the public statement. "
                        + "The Lean module derives the co-selected mass, the product bad-green "
                        + "mass, and its repository exponential envelope from those clauses, so "
                        + "the consequences are not repeated as public conjuncts."))),
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

    private static Formula TheoremFormula()
    {
        Formula epsilon = F.Id("epsilon");
        Formula budget = F.Id("m");
        Formula deployment = Mu;
        Formula coSelected = F.Id("Wc");
        Formula independent = F.Id("Wi");
        Formula index = F.Id("j");
        Formula input = F.Id("input");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula boolType = F.Id("Bool");
        Formula pmfBool = Call("PMF", boolType);
        Formula finBudget = Call("Fin", budget);
        Formula suiteType = Arrow(finBudget, boolType);
        Formula jointLawType = Call("Measure", suiteType);
        Formula world = F.Id("World");
        Formula worldType = Seq(
            Open, jointLawType, Close, Sp, Times, Sp, Open, suiteType, Close);
        Formula implementation = F.Id("implementation");
        Formula expected = F.Id("expected");
        Formula suiteCo = Field(coSelected, 2);
        Formula suiteIndependent = Field(independent, 2);
        Formula lawCo = Field(coSelected, 1);
        Formula lawIndependent = Field(independent, 1);
        Formula implementationDefinition = Seq(
            implementation, Colon, Sp, Arrow(boolType, boolType), Sp, Eq, Sp,
            Open, Underscore, Sp, Mapsto, Sp, F.Id("false"), Close);
        Formula expectedDefinition = Seq(
            expected, Colon, Sp, Arrow(boolType, boolType), Sp, Eq, Sp, F.Id("id"));
        Formula worldDefinition = Seq(world, Sp, Eq, Sp, worldType);
        Formula coordinateProductLaw = Call(
            "pi", Seq(index, Sp, Mapsto, Sp, Call("toMeasure", deployment)));
        Formula loss = Seq(
            Sum, Underscore, Grp(input, Colon, Sp, boolType), Sp,
            F.Text, Grp(F.Id("if"), Sp),
            Apply(implementation, input), Sp, Eq, Sp, Apply(expected, input),
            F.Text, Grp(Sp, F.Id("then"), Sp), D(0),
            F.Text, Grp(Sp, F.Id("else"), Sp),
            Call("toReal", Apply(deployment, input)));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, epsilon, Colon, Sp, real, Comma, Sp,
            budget, Colon, Sp, natural, Comma, RowBreak, Grp(),
            D(0), Sp, Lt, Sp, epsilon, Sp, Land, Sp,
            epsilon, Sp, Lt, Sp, D(1), Sp, Rightarrow, RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            implementationDefinition, Comma, RowBreak, Grp(),
            expectedDefinition, Comma, RowBreak, Grp(),
            worldDefinition, Close, Semi, RowBreak, Grp(),
            Exists, Sp, deployment, Colon, Sp, pmfBool, Comma, Sp,
            coSelected, Comma, Sp, independent, Colon, Sp, world, Comma,
            RowBreak, Grp(),
            suiteCo, Sp, Eq, Sp, suiteIndependent, Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, index, Comma, Sp,
            Apply(suiteCo, index), Sp, Eq, Sp, F.Id("false"), Close,
            Sp, Land, RowBreak, Grp(),
            lawCo, Sp, Eq, Sp, Call("dirac", suiteCo),
            Sp, Land, RowBreak, Grp(),
            lawIndependent, Sp, Eq, Sp, coordinateProductLaw,
            Sp, Land, RowBreak, Grp(),
            loss, Sp, Eq, Sp,
            new Formula.Fraction(Seq(D(1), Plus, epsilon), D(2)), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
