using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeRegrade;

internal sealed class SemanticSketchTargetLaunderingBridgeDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeRegrade/"
            + "SemanticSketchTargetLaunderingBridge."
            + "semantic_sketch_target_laundering_iff_body_and_timestamp";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact temporal bridge identifies sketch laundering with body laundering plus its report timestamp.",
        H("Semantic Sketch Target-Laundering Bridge"),
        Blocks(Describe.Lean(
            DescribeId.Create("semantic-sketch-target-laundering-bridge"),
            DeclarationHandle.Create(Declaration),
            H("Sketch laundering is body laundering plus the sketch timestamp"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary semantic regrade frame, commitments, evidence, and "
                        + "regrade report, assume the explicit RegradeTemporalBridge equating "
                        + "freeze visibility with strict arrival before the commitment freeze.")),
                Paragraph(Text(
                    "The bridge converts only the temporal clause. Report identity, original "
                        + "attribution, and the closed nonempty protected-coordinate witness "
                        + "bundle remain unchanged, while the sketch-only report timestamp is "
                        + "retained as the additional conjunct.")),
                Paragraph(Text(
                    "This discharges obligation 57.2-D from definition-escape-completion-theory "
                        + "atom generic-residual-b41cab36c0664076d72484d1cc20fe14a1f832df6131b"
                        + "1650816f3eb19119363."))),
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
        Formula bridge = F.Id("bridge");
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
        Formula bridgeType = Call("RegradeTemporalBridge", frame);
        Formula reportValue = Seq(regrade, Dot, F.Id("report"));
        Formula occurredAt = Seq(
            frame, Dot, F.Id("reportOccurredAt"), Open, reportValue, Close);
        Formula freezeTime = Seq(
            frame, Dot, F.Id("freezeTime"), Open, newCommitment, Close);

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
            frame, Colon, Sp, frameType, Comma, RowBreak, Grp(),
            oldCommitment, Comma, Sp, newCommitment, Colon, Sp,
            commitment, Comma, Sp,
            suppliedEvidence, Colon, Sp, evidence, Comma, RowBreak, Grp(),
            regrade, Colon, Sp, regradeType, Comma, Sp,
            bridge, Colon, Sp, bridgeType, Comma, RowBreak, Grp(),
            Call(
                "SemanticSketchTargetLaunderingAt",
                frame,
                oldCommitment,
                newCommitment,
                suppliedEvidence,
                regrade),
            Sp, Iff, RowBreak, Grp(),
            Call(
                "SemanticTargetLaunderingAt",
                frame,
                oldCommitment,
                newCommitment,
                suppliedEvidence,
                regrade),
            Sp, Land, RowBreak, Grp(),
            occurredAt, Sp, Eq, Sp, freezeTime, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
