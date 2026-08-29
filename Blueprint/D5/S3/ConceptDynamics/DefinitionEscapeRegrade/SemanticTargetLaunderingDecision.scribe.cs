using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeRegrade;

internal sealed class SemanticTargetLaunderingDecisionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeRegrade/"
            + "SemanticTargetLaunderingDecision."
            + "target_laundering_decision_nonempty";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Decidable protected coordinates and report conditions yield an exact laundering decision.",
        H("Semantic Target-Laundering Decision"),
        Blocks(Describe.Lean(
            DescribeId.Create("semantic-target-laundering-decision"),
            DeclarationHandle.Create(Declaration),
            H("The laundering predicate has a certified Boolean decision"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary regrade semantic frame, commitment and evidence equality, "
                        + "each of the seven protected-coordinate equalities, and strict time "
                        + "comparison are decidable. No finite carrier, verdict equality, "
                        + "inhabited commitment type, or verdict-change premise is used.")),
                Paragraph(Text(
                    "Dependent protected-coordinate extensionality first supplies equality "
                        + "decision for the complete coordinate record. The frozen body-level "
                        + "characterization then decides the laundering predicate, and the "
                        + "returned Boolean carries its exact correctness equivalence.")),
                Paragraph(Text(
                    "The same module transcribes the standard interpreter from the existing "
                        + "prospective-commitment and regrade-report carriers and proves a named "
                        + "specialization through that interpreter. This discharges obligation "
                        + "57.2-E from definition-escape-completion-theory atom generic-residual-"
                        + "18a12b09c5e901f1df86ba136d7ef48402e6fbabd170dd510c85c64d00c8a9f8."))),
            DescribeRole.Theorem))));

    private static Formula CoordinateType(
        Formula targetChain,
        Formula domain,
        Formula epsilon,
        Formula condition,
        Formula comparator,
        Formula baseline,
        Formula weightSpec) =>
        Call(
            "ProtectedCoordinates",
            targetChain,
            domain,
            epsilon,
            condition,
            comparator,
            baseline,
            weightSpec);

    private static Formula TheoremFormula()
    {
        Formula commitment = F.Id("Commitment");
        Formula evidence = F.Id("Evidence");
        Formula verdict = F.Id("Verdict");
        Formula time = F.Id("Time");
        Formula targetChain = F.Id("TargetChain");
        Formula domain = F.Id("Domain");
        Formula epsilon = F.Id("Epsilon");
        Formula condition = F.Id("Condition");
        Formula comparator = F.Id("Comparator");
        Formula baseline = F.Id("Baseline");
        Formula weightSpec = F.Id("WeightSpec");
        Formula report = F.Id("Report");
        Formula frame = F.Id("S");
        Formula oldCommitment = F.Id("oldK");
        Formula newCommitment = F.Id("newK");
        Formula suppliedEvidence = F.Id("Z");
        Formula regrade = F.Id("regrade");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula coordinates = CoordinateType(
            targetChain,
            domain,
            epsilon,
            condition,
            comparator,
            baseline,
            weightSpec);
        Formula frameType = Call(
            "RegradeSemantics",
            commitment,
            evidence,
            verdict,
            time,
            coordinates,
            report);
        Formula regradeType = Call("SemanticRegrade", frame);
        Formula strictTimeRelation = Seq(
            Open,
            Cdot,
            Sp,
            Lt,
            Sp,
            Cdot,
            Close,
            Colon,
            Sp,
            time,
            Sp,
            To,
            Sp,
            time,
            Sp,
            To,
            Sp,
            F.Id("Prop"));
        Formula decisionType = Call(
            "TargetLaunderingDecision",
            frame,
            oldCommitment,
            newCommitment,
            suppliedEvidence,
            regrade);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            commitment, Comma, Sp,
            evidence, Comma, Sp,
            verdict, Comma, Sp,
            time, Comma, Sp,
            targetChain, Comma, Sp,
            domain, Comma, Sp,
            epsilon, Comma, Sp,
            condition, Comma, Sp,
            comparator, Comma, Sp,
            baseline, Comma, Sp,
            weightSpec, Comma, Sp,
            report, Colon, Sp, type, Comma, RowBreak, Grp(),
            OpenBracket, Call("LT", time), CloseBracket, Comma, RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", commitment), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", evidence), CloseBracket,
            Comma, RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", targetChain), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", domain), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", epsilon), CloseBracket,
            Comma, RowBreak, Grp(),
            OpenBracket, Call("DecidableEq", condition), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", comparator), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", baseline), CloseBracket,
            Comma, Sp,
            OpenBracket, Call("DecidableEq", weightSpec), CloseBracket,
            Comma, RowBreak, Grp(),
            OpenBracket,
            Call("DecidableRel", strictTimeRelation),
            CloseBracket,
            Comma, RowBreak, Grp(),
            frame, Colon, Sp, frameType, Comma, RowBreak, Grp(),
            oldCommitment, Comma, Sp, newCommitment, Colon, Sp,
            commitment, Comma, Sp,
            suppliedEvidence, Colon, Sp, evidence, Comma, RowBreak, Grp(),
            regrade, Colon, Sp, regradeType, Comma, RowBreak, Grp(),
            Call("Nonempty", decisionType), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
