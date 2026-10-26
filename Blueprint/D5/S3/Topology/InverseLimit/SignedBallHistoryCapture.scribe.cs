using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedBallHistoryCaptureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original whole signed sequences, launched support families and proper-stage historical limits.",
        H("Signed historical capture"),
        Blocks(
            Paragraph(Text(
                "The diagram has all proper ordinals below omega-one as indices, with arrows reversed. "
                + "Its objects and the point of its actual limit cone are profinite spaces. "
                + "BirthStage contains only the stages at or above omega. RawHistory stores the original onto support enumerations U, support families V and onto whole-sequence signed enumerations nu on those stages. "
                + "No support enumeration is required at an earlier finite stage. The launch law identifies an original V(theta) with the literal pullback of an enumerated U(b,i) at a later proper theta.")),
            Paragraph(Text(
                "Fix a regular signed sequence of variation mass one with disjoint nonempty clopen supports and positive Jordan mass at least one half. CountableSignedMeasureReflection.exists_common_stage supplies one proper b at or above omega that reflects those same supports and preserves the variation and Jordan whole masses. "
                + "Surjectivity of U(b) selects one support-family index i. The launch law supplies theta greater than b. "
                + "Cone naturality identifies the final b projection with the composite through theta. Two variation contractions force every theta pushforward to have mass exactly one. "
                + "Preservation of signed whole mass and the sum and difference identities for the Jordan masses preserve the positive-half bound. "
                + "Continuous pushforward of regular variation, together with exact mass preservation, gives regular variation downstairs. Variation contraction proves complement nullity on the actual launched supports.")),
            Paragraph(Text(
                "The entire theta pushforward sequence is therefore one BornData value. The original total onto nu(theta) chooses a single d whose equality holds for every natural index. "
                + "The label d may exceed theta. Eligible(theta,d) consists exactly of the proper c greater than max(theta,d). "
                + "At every such c, literal projection composition and the same two-contraction argument prove a regular norm-one lift of that original birth, with the required inverse-image carrying. "
                + "The proper-stage F law applies to these actual projected sequences.")),
            Paragraph(Text(
                "The original disjoint reservoirs and the historical J sets determine two distinct free ultrafilters before any continuous test is selected. "
                + "Finite directedness modulo finite sets suffices; no common infinite J or pseudointersection is used. "
                + "Each final continuous real test factors exactly through its own eligible proper stage by CountableContinuousReflection.exists_stage. "
                + "Pushforward integration transfers proper-stage convergence to that final test. The fixed ultrafilters then agree under every weak-dual evaluation of every continuous extension of the signed sequence.")),
            Paragraph(Text(
                "The resulting implication is exactly SignedBallReduction.SignedClopenCollision for the actual cone point. Simultaneous signed-measure reflection is a proved supplier, with the same reflected supports. "
                + "An arbitrary signed pushforward need not preserve its variation mass. RawHistory does not assume such an isometry or final-test convergence. "
                + "The historical calculation is an application of the cited suppliers. It does not construct a CH history, establish AH, or settle Problem 8.2.")),
            Describe.Lean(DescribeId.Create("exists-original-birth"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.exists_original_birth"),
                H("Capture the entire original signed birth"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every proper-stage profinite diagram F, cone C, and RawHistory H, take a regular signed sequence s on C.pt of variation mass one and positive Jordan mass at least one half. Fix a birth b and support family W at b, whose final pullbacks carry s, and assume the b pushforwards still have mass one. There are one original birth theta greater than b and one whole label d such that for every natural n the original H.nu(theta,d,n) is exactly s(n) pushed to theta, and the original H.V(theta,n) pullback carries s(n). The proof body is unchanged; the helper is public for the actual endpoint consumer."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("projected-lift"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.projected_lift"),
                H("Every eligible projection is the original norm-one lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For any such F, C and H, regular norm-one signed sequence s, original birth theta and label d, suppose every theta pushforward is H.nu(theta,d,n), with variation carried by the original theta support pullbacks. At every eligible proper c greater than max(theta,d), the c pushforwards have regular variation and mass exactly one, push along the literal bond back to those original birth measures at every n, and are variation-null off the pulled-back original theta supports. The proof body is unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("signed-clopen-collision"),
                DeclarationHandle.Create("D5/S3/Topology/InverseLimit/SignedBallHistoryCapture.signed_clopen_collision"),
                H("Historical F gives the signed collision criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every F with nonempty profinite objects, actual limit cone C, all diagram maps surjective, and RawHistory H, SignedClopenCollision holds on C.pt. Thus every admissible normalized regular signed sequence on disjoint nonempty clopen supports and every continuous ultrafilter extension of its signed functionals admit two distinct free ultrafilters with the same extension value. The ultrafilters are chosen before the final continuous scalar test, and each test factors through its own eligible proper stage. The publicization retains the unchanged proof and permits the actual CH endpoint theorem to consume it."))),
                DescribeRole.Theorem))));
}
