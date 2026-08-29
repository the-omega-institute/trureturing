using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscapeRegrade;

internal sealed class SemanticTargetLaunderingBundleEliminationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/DefinitionEscapeRegrade/"
            + "SemanticTargetLaunderingBundleElimination."
            + "semantic_target_laundering_iff_protected_coordinates_ne";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Body-level semantic target laundering eliminates its coordinate witness bundle.",
        H("Semantic Target-Laundering Bundle Elimination"),
        Blocks(Describe.Lean(
            DescribeId.Create("semantic-target-laundering-bundle-elimination"),
            DeclarationHandle.Create(Declaration),
            H("Body-level laundering is characterized by protected-coordinate inequality"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The semantic frame reads protected coordinates, evaluations, timing, "
                        + "and report fields from existing carriers. SemanticTargetLaunderingAt "
                        + "retains report identity, strict post-arrival timing, attribution to "
                        + "the original commitment, and a closed nonempty coordinate witness "
                        + "bundle.")),
                Paragraph(Text(
                    "The frozen coordinate-bundle characterization replaces only that final "
                        + "bundle with inequality of the complete protected-coordinate records. "
                        + "No report condition, timing condition, or attribution condition is "
                        + "removed, and neither verdict change nor a report-timestamp equality "
                        + "is assumed.")),
                Paragraph(Text(
                    "This discharges obligation 57.2-C from definition-escape-completion-theory "
                        + "atom generic-residual-c42f6cc861bde491da258e3f06a84362929990f099ec"
                        + "729da096b9d25774bb1b."))),
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
        Formula reportValue = Seq(regrade, Dot, F.Id("report"));
        Formula attributedTo = Seq(
            frame, Dot, F.Id("reportAttributedTo"), Open, reportValue, Close);
        Formula oldCoordinates = Seq(
            frame, Dot, F.Id("protected"), Open, oldCommitment, Close);
        Formula newCoordinates = Seq(
            frame, Dot, F.Id("protected"), Open, newCommitment, Close);

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
            OpenBracket, Call("LT", time), CloseBracket, Comma, Sp,
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
            frame, Colon, Sp, frameType, Comma, RowBreak, Grp(),
            oldCommitment, Comma, Sp, newCommitment, Colon, Sp,
            commitment, Comma, Sp,
            suppliedEvidence, Colon, Sp, evidence, Comma, Sp,
            regrade, Colon, Sp, regradeType, Comma, RowBreak, Grp(),
            Call(
                "SemanticTargetLaunderingAt",
                frame,
                oldCommitment,
                newCommitment,
                suppliedEvidence,
                regrade),
            Sp, Iff, RowBreak, Grp(),
            Call(
                "SemanticRegradeAt",
                regrade,
                oldCommitment,
                newCommitment,
                suppliedEvidence),
            Sp, Land, RowBreak, Grp(),
            Call("PostArrivalSemanticRegrade", frame, regrade),
            Sp, Land, RowBreak, Grp(),
            attributedTo, Sp, Eq, Sp, oldCommitment,
            Sp, Land, RowBreak, Grp(),
            oldCoordinates, Sp, Neq, Sp, newCoordinates, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
