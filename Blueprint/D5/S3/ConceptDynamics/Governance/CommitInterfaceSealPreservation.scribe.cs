using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Governance;

internal sealed class CommitInterfaceSealPreservationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Governance/CommitInterfaceSealPreservation."
            + "commit_interface_seal_and_artifact_preservation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A commit interface seals every digest coordinate and confines committed artifacts "
            + "to the input bundle, decision candidates, and dependency closure.",
        H("Commit-Interface Seal Preservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("commit-interface-seal-and-artifact-preservation"),
                DeclarationHandle.Create(Declaration),
                H("Commit outputs preserve their seal and artifact boundaries"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed statement unfolds the Lean let-bound commitment and "
                            + "output seal as the first and dependent second projections of "
                            + "commitStep(I,B).")),
                    Paragraph(Text(
                        "The first four clauses expose the seal fields: the digest consumes the "
                            + "whole commitment together with its freeze event and dependency "
                            + "closure, and the stored commitment, event, and closure equal those "
                            + "same inputs.")),
                    Paragraph(Text(
                        "The candidate equality is supplied by CommitInterface. For every "
                            + "committed artifact, input-bundle membership follows from the "
                            + "interface, while candidate and dependency-closure membership come "
                            + "from the imported ProspectiveCommitment carrier.")),
                    Paragraph(Text(
                        "The module also constructs a finite Unit-valued interface and nonempty "
                            + "bundle, so the quantified interface and artifact domains are "
                            + "machine-checked as inhabited."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Member(Formula value, Formula collection) =>
        Seq(value, Sp, InMacro, Sp, collection);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula roundState = F.Id("RoundState");
        Formula digestType = F.Id("Digest");
        Formula eventId = F.Id("EventId");
        Formula evidence = F.Id("Evidence");
        Formula round = F.Id("Round");
        Formula artifactType = F.Id("Artifact");
        Formula time = F.Id("Time");
        Formula targetChain = F.Id("TargetChain");
        Formula domain = F.Id("Domain");
        Formula epsilon = F.Id("Epsilon");
        Formula condition = F.Id("Condition");
        Formula comparator = F.Id("Comparator");
        Formula testPlan = F.Id("TestPlan");
        Formula baseline = F.Id("Baseline");
        Formula weightSpec = F.Id("WeightSpec");
        Formula roundValue = F.Id("n");
        Formula interfaceValue = F.Id("I");
        Formula bundle = F.Id("B");
        Formula artifact = F.Id("a");

        Formula interfaceType = Call("CommitInterface", roundState, digestType, eventId,
            evidence, round, artifactType, time, targetChain, domain, epsilon, condition,
            comparator, testPlan, baseline, weightSpec, roundValue);
        Formula bundleType = Call("CandidateBundle", artifactType);
        Formula commitOutput = Call("commitStep", interfaceValue, bundle);
        Formula commitment = Call("fst", commitOutput);
        Formula outputSeal = Call("snd", commitOutput);
        Formula freezeEvent = Call("freezeEvent", Call("adjudication", commitment));
        Formula dependencyClosure =
            Call("dependencyClosure", Call("adjudication", commitment));
        Formula candidates = Call("candidates", Call("decision", commitment));
        Formula artifacts = Call("artifacts", bundle);
        Formula committedArtifacts = Call("committedArtifacts", commitment);

        Formula artifactBoundary = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("a", artifactType)],
            Implies(
                Member(artifact, committedArtifacts),
                And(
                    Member(artifact, artifacts),
                    And(Member(artifact, candidates),
                        Member(artifact, dependencyClosure)))));
        Formula conclusion = And(
            EqualTo(
                Call("digest", outputSeal),
                Call("digestOf", interfaceValue, commitment, freezeEvent,
                    dependencyClosure)),
            And(
                EqualTo(Call("sealedCommitment", outputSeal), commitment),
                And(
                    EqualTo(Call("sealedFreezeEvent", outputSeal), freezeEvent),
                    And(
                        EqualTo(Call("sealedDependencyClosure", outputSeal),
                            dependencyClosure),
                        And(EqualTo(candidates, artifacts), artifactBoundary)))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("RoundState", type),
                Bound("Digest", type),
                Bound("EventId", type),
                Bound("Evidence", type),
                Bound("Round", type),
                Bound("Artifact", type),
                Bound("Time", type),
                Bound("TargetChain", type),
                Bound("Domain", type),
                Bound("Epsilon", type),
                Bound("Condition", type),
                Bound("Comparator", type),
                Bound("TestPlan", type),
                Bound("Baseline", type),
                Bound("WeightSpec", type),
                Bound("n", round),
                Bound("I", interfaceType),
                Bound("B", bundleType),
            ],
            conclusion));
    }
}
