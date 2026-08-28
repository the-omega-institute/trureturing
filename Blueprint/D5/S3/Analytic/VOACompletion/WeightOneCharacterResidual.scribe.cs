using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.VOACompletion;

internal sealed class WeightOneCharacterResidualDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Subtracting the weight-one character makes every Niemeier scalar character equal to J, "
            + "while the untwined scalar remains blind to finer structure.",
        H("Weight-One Character Residual for Niemeier VOAs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("weight-one-character-residual"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/VOACompletion/WeightOneCharacterResidual."
                        + "weight_one_character_residual"),
                H("Weight-one subtraction gives the universal character J"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Niemeier carrier keeps the two source-named root systems A5^4 D4 and "
                            + "D4^6 as distinct constructors, alongside the complete list of twenty-four "
                            + "named Niemeier root-system constructors.")),
                    Paragraph(Text(
                        "The supplied character and weight-one formulas are the preceding source "
                            + "identities Z = J + 24(h + 1) and dim(V1) = 24(h + 1). Pointwise "
                            + "subtraction proves the first conclusion. The equal Coxeter values and "
                            + "equal Theta witness give the concrete scalar collision.")),
                    Paragraph(Text(
                        "The central-charge and holomorphicity guards remain visible in the general "
                            + "VOA clause. Separate structural and classification witnesses record "
                            + "why an untwined scalar character cannot recover multiplication, OPE, "
                            + "group-action, Lie, orbifold, or other fine data."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Forall(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula TheoremFormula()
    {
        Formula J = F.Id("J");
        Formula scalar = F.Id("scalarCharacter");
        Formula dimension = F.Id("weightOneDimension");
        Formula coxeter = F.Id("coxeterNumber");
        Formula theta = F.Id("theta");
        Formula structure = F.Id("structureData");
        Formula classification = F.Id("classificationData");
        Formula niemeier = Call("NiemeierVOA");
        Formula character = Call("ScalarCharacter");
        Formula a5 = Call("A5FourD4");
        Formula d4 = Call("D4Six");

        Formula residual = Forall("N", niemeier,
            Equal(Call("weightOneResidual", Call("apply", scalar, F.Id("N")),
                Call("apply", dimension, F.Id("N"))), J));
        Formula thetaCollision = Call("sameThetaDifferentRoot", theta);
        Formula general = Forall("V", Call("VOAData"),
            Implies(
                And(Equal(Call("centralCharge", F.Id("V")), Num(24)),
                    Call("holomorphic", F.Id("V"))),
                Equal(Call("scalarCharacter", F.Id("V")),
                    Call("addDimension", J, Call("weightOneDimension", F.Id("V"))))));
        Formula structuralBlindness = Call("scalarBlindToStructure", scalar, structure);
        Formula refinement = Call("classificationNeedsRefinement", scalar, classification);
        Formula conclusions = And(residual,
            And(thetaCollision, And(general, And(structuralBlindness, refinement))));

        Formula characterPremise = Forall("N", niemeier,
            Equal(Call("apply", scalar, F.Id("N")),
                Call("jPlusTwentyFourTimesCoxeterPlusOne", J, Call("apply", coxeter, F.Id("N")))));
        Formula dimensionPremise = Forall("N", niemeier,
            Equal(Call("apply", dimension, F.Id("N")),
                Call("twentyFourTimesCoxeterPlusOne", Call("apply", coxeter, F.Id("N")))));
        Formula coxeterPremises = And(
            Equal(Call("apply", coxeter, a5), Num(6)),
            Equal(Call("apply", coxeter, d4), Num(6)));
        Formula thetaPremise = Equal(Call("apply", theta, a5), Call("apply", theta, d4));
        Formula modularityPremise = Forall("V", Call("VOAData"),
            Implies(
                And(Equal(Call("centralCharge", F.Id("V")), Num(24)),
                    Call("holomorphic", F.Id("V"))),
                Equal(Call("scalarCharacter", F.Id("V")),
                    Call("addDimension", J, Call("weightOneDimension", F.Id("V"))))));
        Formula structuralPremise = NotEqual(Call("apply", structure, a5),
            Call("apply", structure, d4));
        Formula classificationPremise = NotEqual(Call("apply", classification, a5),
            Call("apply", classification, d4));
        Formula sourcePremises = And(characterPremise,
            And(dimensionPremise,
                And(coxeterPremises,
                    And(thetaPremise,
                        And(modularityPremise,
                            And(structuralPremise, classificationPremise))))));

        return Disp(Implies(sourcePremises, conclusions));
    }
}
