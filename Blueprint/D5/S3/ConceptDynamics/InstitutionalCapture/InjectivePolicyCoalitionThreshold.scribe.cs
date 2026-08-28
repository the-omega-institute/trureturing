using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InstitutionalCapture;

internal sealed class InjectivePolicyCoalitionThresholdDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/InstitutionalCapture/InjectivePolicyCoalitionThreshold.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A policy preserving every realized secret distinction has exactly the secret-recovery "
            + "coalition threshold.",
        H("Injective Policy Coalition Threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("injective-policy-and-secret-thresholds-agree"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "injective_policy_coalition_threshold"),
                H("Policy implementation and secret recovery have the same threshold"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Coalition readouts, their attainable cardinality sets, and minimum size "
                            + "are imported from the frozen family rather than redeclared.")),
                    Paragraph(Text(
                        "When the secret carrier is inhabited, an inverse on the realized secret "
                            + "image converts policy factorization back to secret factorization. "
                            + "When it is empty, the source state type is empty and both natural "
                            + "infima are zero.")),
                    Paragraph(Text(
                        "No finite-participant instance or full-coalition recovery premise is "
                            + "needed; the equality holds for every finite coalition inside an "
                            + "arbitrary participant type."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ExistsPolicyFactor(
        Formula stateType,
        Formula secretType,
        Formula policyType,
        Formula secret,
        Formula policy)
    {
        Formula policyMap = F.Id("j");
        Formula factorization = Equal(
            policy,
            Call("compose", policyMap, secret));
        Formula injectivity = Call(
            "InjOn", policyMap, Call("range", secret));
        return new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("j", Arrow(secretType, policyType))],
            And(factorization, injectivity));
    }

    private static Formula Minimum(
        Formula participantType,
        Formula share,
        Formula readout,
        Formula coalition)
    {
        Formula property = Grp(
            Lambda, Sp, coalition, Colon, Sp, Call("Finset", participantType), Comma, Sp,
            Call("Refines", readout, Call("coalitionReadout", share, coalition)));
        return Call(
            "minimumCoalitionSize",
            property);
    }

    private static Formula TheoremFormula()
    {
        Formula participantType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula shareType = F.Id("V");
        Formula secretType = F.Id("B");
        Formula policyType = F.Id("U");
        Formula share = F.Id("share");
        Formula secret = F.Id("secret");
        Formula policy = F.Id("policy");
        Formula coalition = F.Id("K");
        Formula premise = ExistsPolicyFactor(
            stateType, secretType, policyType, secret, policy);
        Formula conclusion = Equal(
            Minimum(participantType, share, policy, coalition),
            Minimum(participantType, share, secret, coalition));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", F.Id("Type")),
                Bound("X", F.Id("Type")),
                Bound("V", F.Id("Type")),
                Bound("B", F.Id("Type")),
                Bound("U", F.Id("Type")),
                Bound("decI", Call("DecidableEq", participantType)),
                Bound("share", Arrow(participantType, Arrow(stateType, shareType))),
                Bound("secret", Arrow(stateType, secretType)),
                Bound("policy", Arrow(stateType, policyType)),
            ],
            new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
