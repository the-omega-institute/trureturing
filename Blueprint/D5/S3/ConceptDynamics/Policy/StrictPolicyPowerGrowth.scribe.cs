using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Policy;

internal sealed class StrictPolicyPowerGrowthDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separating one coarse fiber with a finer readout strictly increases policy power.",
        H("Strict Policy Power Growth"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-policy-power-growth"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Policy/StrictPolicyPowerGrowth."
                        + "strict_policy_power_growth"),
                H("A separated coarse fiber yields a genuinely new policy"),
                StatementSource.FromAuthor(GrowthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let two states have the same coarse coordinate but distinct fine "
                            + "coordinates. Given two distinct actions, a decision rule on the "
                            + "fine coordinate can assign one action to the fine coordinate of "
                            + "the first state and the other action everywhere else. The induced "
                            + "state policy therefore distinguishes the two states.")),
                    Paragraph(Text(
                        "Every policy available from the coarse readout factors through its "
                            + "coarse coordinate, so it must take equal values on those states. "
                            + "Consequently the separating policy belongs to the fine capability "
                            + "but not the coarse capability, while all coarse policies satisfy "
                            + "the universal non-separation conclusion.")),
                    Paragraph(Text(
                        "The result needs neither surjectivity nor a global strict-refinement "
                            + "hypothesis: one explicitly separated pair inside a coarse fiber "
                            + "already witnesses strict local growth of policy power."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Capability(Formula readout, Formula actionType) =>
        Call("policyCapability", readout, actionType);

    private static Formula GrowthFormula()
    {
        Formula source = F.Id("X");
        Formula coarseType = F.Id("C");
        Formula fineType = F.Id("D");
        Formula actionType = F.Id("U");
        Formula readoutC = Subscript(F.Id("q"), coarseType);
        Formula readoutD = Subscript(F.Id("q"), fineType);
        Formula firstState = F.Id("x");
        Formula secondState = F.Id("y");
        Formula firstAction = Subscript(F.Id("u"), D(0));
        Formula secondAction = Subscript(F.Id("u"), D(1));
        Formula finePolicy = F.Id("policy");
        Formula coarsePolicy = F.Id("coarsePolicy");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));

        Formula sameCoarseFiber = Seq(
            Apply(readoutC, firstState), Sp, Eq, Sp, Apply(readoutC, secondState));
        Formula separatedByFineReadout = Seq(
            Apply(readoutD, firstState), Sp, Neq, Sp, Apply(readoutD, secondState));
        Formula twoActions = Seq(
            Exists, Sp, firstAction, Comma, Sp, secondAction,
            Colon, Sp, actionType, Comma, Sp,
            firstAction, Sp, Neq, Sp, secondAction);
        Formula premise = Seq(
            sameCoarseFiber, Sp, Land, Sp,
            separatedByFineReadout, Sp, Land, Sp,
            Grp(twoActions));

        Formula separatingFinePolicy = Seq(
            Exists, Sp, finePolicy, Colon, Sp, Arrow(source, actionType), Comma, Sp,
            finePolicy, Sp, InMacro, Sp, Capability(readoutD, actionType), Sp, Land, Sp,
            Neg, Grp(finePolicy, Sp, InMacro, Sp, Capability(readoutC, actionType)),
            Sp, Land, Sp,
            Apply(finePolicy, firstState), Sp, Neq, Sp, Apply(finePolicy, secondState));
        Formula coarseNonSeparation = Seq(
            Forall, Sp, coarsePolicy, Colon, Sp, Arrow(source, actionType), Comma, Sp,
            coarsePolicy, Sp, InMacro, Sp, Capability(readoutC, actionType),
            Sp, Rightarrow, Sp,
            Apply(coarsePolicy, firstState), Sp, Eq, Sp,
            Apply(coarsePolicy, secondState));

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coarseType, Comma, Sp, fineType,
            Comma, Sp, actionType, Colon, Sp, type, Comma, Sp,
            readoutC, Colon, Sp, Arrow(source, coarseType), Comma, Sp,
            readoutD, Colon, Sp, Arrow(source, fineType), Comma, Sp,
            firstState, Comma, Sp, secondState, Colon, Sp, source, Comma, Sp,
            Grp(premise), Sp, Rightarrow, Sp,
            Grp(separatingFinePolicy), Sp, Land, Sp, Grp(coarseNonSeparation), Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
