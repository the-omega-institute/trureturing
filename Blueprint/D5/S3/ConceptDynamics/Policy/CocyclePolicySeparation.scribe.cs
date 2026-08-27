using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Policy;

internal sealed class CocyclePolicySeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cocycle accounting does not determine which legal action a policy selects.",
        H("Cocycle And Policy Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("cocycle-does-not-select-policy"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Policy/CocyclePolicySeparation."
                    + "cocycle_does_not_select_policy"),
            H("Cocycle composition leaves policy choice nonunique"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The hidden-jump construction records visible agreement, the "
                        + "endpoint/cocycle equivalence, and an explicit endpoint residual "
                        + "when the selected jumps disagree.")),
                Paragraph(Text(
                    "The same public model carries a permitted-outcome relation with two "
                        + "distinct outcomes in one public-law fiber. Consequently the "
                        + "cocycle law supplies composition and accounting, but no unique "
                        + "policy choice."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Call(name, type), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula unitIndex = F.Id("U");
        Formula solenoid = F.Id("Sigma");
        Formula caseType = F.Id("Case");
        Formula publicFact = F.Id("PublicFact");
        Formula outcome = F.Id("Outcome");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula hiddenCoordinates = F.Id("HiddenJumpCoordinates");
        Formula addCircle = Call("AddCircle", D(1));
        Formula projection = F.Id("projection");
        Formula hiddenEquiv = F.Id("hiddenEquiv");
        Formula sectionAlpha = F.Id("sectionAlpha");
        Formula sectionBeta = F.Id("sectionBeta");
        Formula sectionGamma = F.Id("sectionGamma");
        Formula jumpAlphaBeta = F.Id("jumpAlphaBeta");
        Formula jumpBetaGamma = F.Id("jumpBetaGamma");
        Formula jumpAlphaGamma = F.Id("jumpAlphaGamma");
        Formula publicLaw = F.Id("publicLaw");
        Formula admissible = F.Id("admissible");
        Formula permitted = F.Id("permitted");
        Formula fact = F.Id("b");
        Formula point = F.Id("u");
        Formula left = F.Id("leftOutcome");
        Formula right = F.Id("rightOutcome");
        Formula witness = F.Id("x");
        Formula chosen = F.Id("candidate");

        Formula sectionType = Arrow(unitIndex, solenoid);
        Formula jumpType = Arrow(unitIndex, hiddenCoordinates);
        Formula projectionType = Call("AddMonoidHom", solenoid, addCircle);
        Formula hiddenType = Call("AdditiveEquiv", hiddenCoordinates, Call("ker", projection));
        Formula projectionSurjective = Call("Surjective", projection);
        Formula hAlphaBeta = Seq(
            F.Id("hAlphaBeta"), Colon, Sp, Forall, Sp, point, Comma, Sp,
            Apply(sectionBeta, point), Sp, Eq, Sp,
            Apply(sectionAlpha, point), Sp, Plus, Sp,
            Apply(hiddenEquiv, Apply(jumpAlphaBeta, point)));
        Formula hBetaGamma = Seq(
            F.Id("hBetaGamma"), Colon, Sp, Forall, Sp, point, Comma, Sp,
            Apply(sectionGamma, point), Sp, Eq, Sp,
            Apply(sectionBeta, point), Sp, Plus, Sp,
            Apply(hiddenEquiv, Apply(jumpBetaGamma, point)));
        Formula multipleOutcomes = Seq(
            Exists, Sp, left, Comma, Sp, right, Colon, Sp, outcome, Comma, Sp,
            left, Sp, Neq, Sp, right, Sp, Land, Sp,
            Open, Exists, Sp, witness, Colon, Sp, caseType, Comma, Sp,
            Apply(admissible, witness), Sp, Land, Sp,
            Apply(publicLaw, witness), Sp, Eq, Sp, fact, Sp, Land, Sp,
            Apply(Apply(permitted, witness), left), Close, Sp, Land, Sp,
            Exists, Sp, witness, Colon, Sp, caseType, Comma, Sp,
            Apply(admissible, witness), Sp, Land, Sp,
            Apply(publicLaw, witness), Sp, Eq, Sp, fact, Sp, Land, Sp,
            Apply(Apply(permitted, witness), right));
        Formula visible = Seq(
            Forall, Sp, point, Comma, Sp,
            Apply(projection, Apply(sectionAlpha, point)), Sp, Eq, Sp,
            Apply(projection, Apply(sectionBeta, point)), Sp, Land, Sp,
            Apply(projection, Apply(sectionBeta, point)), Sp, Eq, Sp,
            Apply(projection, Apply(sectionGamma, point)));
        Formula endpoint = Seq(
            Forall, Sp, point, Comma, Sp,
            Apply(sectionGamma, point), Sp, Eq, Sp,
            Apply(sectionAlpha, point), Sp, Plus, Sp,
            Apply(hiddenEquiv, Apply(jumpAlphaGamma, point)));
        Formula cocycle = Seq(
            Forall, Sp, point, Comma, Sp,
            Apply(jumpAlphaGamma, point), Sp, Eq, Sp,
            Apply(jumpAlphaBeta, point), Sp, Plus, Sp,
            Apply(jumpBetaGamma, point));
        Formula mismatch = Seq(
            Exists, Sp, point, Comma, Sp,
            Apply(jumpAlphaGamma, point), Sp, Neq, Sp,
            Apply(jumpAlphaBeta, point), Sp, Plus, Sp,
            Apply(jumpBetaGamma, point));
        Formula residual = Seq(
            Exists, Sp, point, Comma, Sp,
            Apply(sectionGamma, point), Sp, Neq, Sp,
            Apply(sectionAlpha, point), Sp, Plus, Sp,
            Apply(hiddenEquiv, Apply(jumpAlphaGamma, point)));
        Formula policyUnique = Seq(
            Exists, Bang, Sp, chosen, Colon, Sp, outcome, Comma, Sp,
            Exists, Sp, witness, Colon, Sp, caseType, Comma, Sp,
            Apply(admissible, witness), Sp, Land, Sp,
            Apply(publicLaw, witness), Sp, Eq, Sp, fact, Sp, Land, Sp,
            Apply(Apply(permitted, witness), chosen));

        return Disp(Seq(
            Forall, Sp, unitIndex, Comma, Sp, solenoid, Comma, Sp,
            caseType, Comma, Sp, publicFact, Comma, Sp, outcome,
            Colon, Sp, type, Comma, Sp,
            Typeclass("Nonempty", unitIndex), Comma, Sp,
            Typeclass("AddCommGroup", solenoid), Comma, Sp,
            projection, Colon, Sp, projectionType, Comma, Sp,
            F.Id("hProjectionSurjective"), Colon, Sp, projectionSurjective, Comma, Sp,
            hiddenEquiv, Colon, Sp, hiddenType, Comma, Sp,
            sectionAlpha, Comma, Sp, sectionBeta, Comma, Sp, sectionGamma,
            Colon, Sp, sectionType, Comma, Sp,
            jumpAlphaBeta, Comma, Sp, jumpBetaGamma, Comma, Sp, jumpAlphaGamma,
            Colon, Sp, jumpType, Comma, Sp,
            hAlphaBeta, Comma, Sp, hBetaGamma, Comma, Sp,
            publicLaw, Colon, Sp, Arrow(caseType, publicFact), Comma, Sp,
            admissible, Colon, Sp, Arrow(caseType, Seq(Operatorname, Grp(F.Id("Prop")))), Comma, Sp,
            permitted, Colon, Sp, Arrow(caseType, Arrow(outcome, Seq(Operatorname, Grp(F.Id("Prop"))))), Comma, Sp,
            fact, Colon, Sp, publicFact, Comma, Sp,
            multipleOutcomes, Sp, Rightarrow, Sp,
            Open, Open, visible, Close, Sp, Land, Sp,
            Open, endpoint, Sp, Iff, Sp, cocycle, Close, Sp, Land, Sp,
            Open, mismatch, Sp, Rightarrow, Sp, residual, Close, Close, Sp, Land, Sp,
            Neg, Open, policyUnique, Close, Dot));
    }
}
