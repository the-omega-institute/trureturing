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
                + "The historical calculation is an application of the cited suppliers. It does not construct a CH history, establish AH, or settle Problem 8.2.")))));
}
