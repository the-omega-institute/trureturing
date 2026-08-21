using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.History.Consensus;

internal sealed class InlineConsensusProtocolFixturesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Named fixtures exercise the fail-closed inline-consensus protocol and are consumed by one aggregate theorem.",
        H("Inline Consensus Protocol Fixtures"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("required-inline-consensus-fixtures-are-aggregate-pinned"),
                DeclarationHandle.Create(
                    "D5/S0/History/Consensus/InlineConsensusProtocolFixtures."
                    + "required_fixture_suite_is_pinned"),
                H("Required fixtures are aggregate-pinned"),
                StatementSource.FromAuthor(Disp(Seq(
                    Left, Open, new Formula.Aligned([
                        Seq(
                            Call("terminationRouter", F.Id("permittedObservation")),
                            Sp, Eq, Sp, F.Id("permitClaim")),
                        Seq(
                            Land, Sp,
                            Call("terminationAdmits", F.Id("permittedObservation")),
                            Sp, Eq, Sp, F.Id("true")),
                        Seq(
                            Land, Sp,
                            Call("terminationAdmits", F.Id("fakeRosterObservation")),
                            Sp, Eq, Sp, F.Id("false")),
                        Seq(
                            Land, Sp,
                            Call("terminationAdmits", F.Id("unsatisfiedObservation")),
                            Sp, Eq, Sp, F.Id("false")),
                        Seq(
                            Land, Sp,
                            Call("terminationAdmits", F.Id("abstainObservation")),
                            Sp, Eq, Sp, F.Id("false")),
                        Seq(
                            Land, Sp,
                            Call("terminationAdmits", F.Id("invalidObservation")),
                            Sp, Eq, Sp, F.Id("false")),
                        Seq(
                            Land, Sp,
                            Call("terminationAdmits", F.Id("missingObservation")),
                            Sp, Eq, Sp, F.Id("false")),
                        Seq(
                            Land, Sp,
                            Call("StrictBelow", F.Id("alwaysAbstain"), F.Id("terminationAdmits"))),
                        Seq(Land, Sp, Call("Sound", F.Id("alwaysAbstain"))),
                        Seq(
                            Land, Sp,
                            Call("StrictBelow", F.Id("terminationAdmits"), F.Id("majorityAdmit"))),
                        Seq(Land, Sp, Neg, Sp, Call("Sound", F.Id("majorityAdmit"))),
                        Seq(Land, Sp, Call("Complete", F.Id("completeObservation"))),
                        Seq(
                            Land, Sp, Neg, Sp,
                            Call("Complete", Call("missingCompletionConjunct", F.Id("carrierExit")))),
                        Seq(
                            Land, Sp, Neg, Sp,
                            Call("Complete", Call("missingCompletionConjunct", F.Id("resultArtifact")))),
                        Seq(
                            Land, Sp, Neg, Sp,
                            Call("Complete", Call("missingCompletionConjunct", F.Id("envelope")))),
                        Seq(
                            Land, Sp, Neg, Sp,
                            Call("Complete", Call("missingCompletionConjunct", F.Id("verdict")))),
                        Seq(
                            Land, Sp, Neg, Sp,
                            Call("Complete", Call("missingCompletionConjunct", F.Id("sentinel")))),
                        Seq(
                            Land, Sp, Forall, Sp, F.Id("proxy"), Comma, Sp,
                            Neg, Sp, Call("Complete", Call("evidenceFromProxyOnly", F.Id("proxy")))),
                        Seq(
                            Land, Sp, Left, Open,
                            Call("priorExposure", F.Id("codexCli")),
                            Sp, Neq, Sp,
                            Call("priorExposure", F.Id("nyxidOracle")),
                            Sp, Land, Sp,
                            Forall, Sp, F.Id("latent"), Comma, Sp,
                            Call("correlatedConclusion", F.Id("codexCli"), F.Id("latent")),
                            Sp, Eq, Sp,
                            Call("correlatedConclusion", F.Id("nyxidOracle"), F.Id("latent")),
                            Right, Close),
                        Seq(
                            Land, Sp,
                            Call("selectCarrier", F.Id("allEligible"), Emptyset),
                            Sp, Eq, Sp, F.Id("codexCli")),
                        Seq(
                            Land, Sp,
                            Call("selectCarrier", F.Id("allEligible"),
                                Seq(OpenBrace, F.Id("codexCli"), CloseBrace)),
                            Sp, Eq, Sp, F.Id("nyxidOracle")),
                        Seq(
                            Land, Sp,
                            Call("selectCarrier",
                                Seq(Left, Open, LambdaLower, Sp, F.Id("carrier"), Comma, Sp,
                                    F.Id("false"), Right, Close),
                                Emptyset),
                            Sp, Eq, Sp, F.Id("abstain")),
                        Seq(
                            Land, Sp, Left, Open, new Formula.Aligned([
                                Seq(
                                    Call("reviewRouter",
                                        Seq(Left, Open, LambdaLower, Sp, F.Id("seat"), Comma, Sp,
                                            F.Id("reject"), Right, Close)),
                                    Sp, Eq, Sp, F.Id("fix")),
                                Seq(
                                    Land, Sp,
                                    Call("reviewRouter",
                                        Seq(Left, Open, LambdaLower, Sp, F.Id("seat"), Comma, Sp,
                                            F.Id("approve"), Right, Close)),
                                    Sp, Eq, Sp, F.Id("done")),
                                Seq(
                                    Land, Sp,
                                    Call("reviewRouter",
                                        Seq(Left, Open, LambdaLower, Sp, F.Id("seat"), Comma, Sp,
                                            F.Id("comment"), Right, Close)),
                                    Sp, Eq, Sp, F.Id("userDecisionOrBoundedPass")),
                            ]), Right, Close),
                        Seq(
                            Land, Sp, Call("card", F.Id("ThinkingSeat")),
                            Sp, Eq, Sp, D(6)),
                        Seq(
                            Land, Sp, Call("card", F.Id("ReviewSeat")),
                            Sp, Eq, Sp, D(3)),
                        Seq(
                            Land, Sp,
                            Call("thinkingSituation", F.Id("allProposeThinkingResults")),
                            Sp, Eq, Sp, F.Id("unanimousActionable")),
                        Seq(
                            Land, Sp,
                            Call("reviewRouter", Call("reviewObservation", F.Id("allRejectReviewResults"))),
                            Sp, Eq, Sp, F.Id("fix")),
                        Seq(
                            Land, Sp, F.Id("allRejectReviewFinal"), Dot, F.Id("reviewExit"),
                            Sp, Eq, Sp, Call("some", F.Id("fix"))),
                        Seq(
                            Land, Sp, Neg, Sp, Left, Open,
                            Exists, Sp, F.Id("final"), Comma, Sp,
                            Call("ProtocolStep", F.Id("fixtureConfig"),
                                F.Id("allRejectReviewFinal"), F.Id("finish"), F.Id("final")),
                            Right, Close),
                        Seq(
                            Land, Sp, Neg, Sp,
                            Call("PassBudgetAuthorized", F.Id("unauthorizedOverBudgetConfig"))),
                        Seq(
                            Land, Sp,
                            Forall, Sp, F.Id("start"), Comma, Sp, F.Id("events"), Comma, Sp,
                            F.Id("final"), Comma, Sp,
                            Neg, Sp, Call("Execution", F.Id("inlineConsensusModel"),
                                F.Id("unauthorizedOverBudgetConfig"), F.Id("start"),
                                F.Id("events"), F.Id("final"))),
                        Seq(
                            Land, Sp,
                            Call("Execution", F.Id("inlineConsensusModel"),
                                F.Id("unavailableIsolationConfig"),
                                Call("initialState", F.Id("unavailableIsolationConfig")),
                                Seq(OpenBracket, Call("abstain", F.Id("intake")), CloseBracket),
                                F.Id("unavailableIsolationFinal"))),
                        Seq(
                            Land, Sp,
                            Forall, Sp, F.Id("state"), Comma, Sp,
                            F.Id("state"), Dot, F.Id("isolation"), Sp, Eq, Sp,
                            F.Id("unavailable"), Sp, Rightarrow, Sp,
                            Forall, Sp, F.Id("final"), Comma, Sp,
                            Neg, Sp, Call("ProtocolStep", F.Id("fixtureConfig"),
                                F.Id("state"), F.Id("finish"), F.Id("final"))),
                    ]), Right, Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The conjunction consumes the termination rows, both competitor witnesses, "
                    + "all five completion failures, forbidden-proxy rejection, the correlated-prior "
                    + "countermodel, carrier-selection rows, the review truth table, fixed role-cardinality "
                    + "checks, all-reject review routing, unauthorized-budget rejection, and the "
                    + "unavailable-isolation execution and finish prohibition. It pins internal model "
                    + "behavior only; correspondence to the external sshx prose remains the "
                    + "digest-pinned snapshot claim in Inline Consensus Optimality."))),
                DescribeRole.Theorem))));
}
