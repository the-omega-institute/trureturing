using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Transport;

internal sealed class ConservativeExtensionAnswerabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Answerability of old questions is reflected and preserved by surjective pullback.",
        H("Conservative Extension Answerability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("answerability-transports-along-surjection"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability."
                        + "answerability_transports_along_surjection"),
                H("Surjective pullback preserves and reflects answerability"),
                StatementSource.FromAuthor(TransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let a new state space project surjectively onto an old state space. "
                            + "An old target readout factors through an old concept exactly when "
                            + "their pullbacks along the projection have the same factorization.")),
                    Paragraph(Text(
                        "The forward direction reuses the old factor map after pullback. For the "
                            + "reverse direction, surjectivity ensures that equality on all new "
                            + "states reflects equality on every old state. Thus the extension "
                            + "neither loses an old answer nor creates a spurious one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonsurjective-pullback-can-hide-unanswerability"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Transport/ConservativeExtensionAnswerability."
                        + "nonsurjective_pullback_can_hide_unanswerability"),
                H("A non-surjective pullback can hide unanswerability"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The one-state projection reaches only false in the old Boolean state "
                            + "space, while the old concept identifies both Boolean states. On "
                            + "the one visible state, the pulled-back identity target is constant "
                            + "and therefore factors through the pulled-back old concept.")),
                    Paragraph(Text(
                        "On the full old state space, the Boolean identity cannot factor through "
                            + "that constant concept: a single factor value would have to equal "
                            + "both false and true. This counterexample shows that surjectivity is "
                            + "essential for reflecting old-state answerability."))),
                DescribeRole.Lemma))));

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula Concept(Formula domain, Formula codomain) =>
        Seq(Operatorname, Grp(F.Id("Concept")), Open, domain, Comma, Sp, codomain, Close);

    private static Formula TransportFormula()
    {
        Formula oldState = F.Id("X");
        Formula newState = F.Id("Y");
        Formula conceptValue = F.Id("Cval");
        Formula targetValue = F.Id("Tval");
        Formula projection = F.Id("p");
        Formula concept = F.Id("C");
        Formula target = F.Id("T");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula oldAnswerability = Call("Refines", target, concept);
        Formula pulledBackAnswerability = Call(
            "Refines",
            Compose(target, projection),
            Compose(concept, projection));

        return Disp(Seq(
            Forall, Sp, oldState, Comma, Sp, newState, Comma, Sp,
            conceptValue, Comma, Sp, targetValue, Colon, Sp, type, Comma, Esc,
            projection, Colon, Sp, newState, Sp, To, Sp, oldState, Comma, Sp,
            concept, Colon, Sp, Concept(oldState, conceptValue), Comma, Sp,
            target, Colon, Sp, Concept(oldState, targetValue), Comma, Esc,
            Call("Surjective", projection), Sp, Rightarrow, Sp,
            Open, oldAnswerability, Sp, Iff, Sp, pulledBackAnswerability, Close, Dot));
    }

    private static Formula CounterexampleFormula()
    {
        Formula projection = F.Id("nonSurjectiveProjection");
        Formula oldConcept = F.Id("constantOldConcept");
        Formula identity = F.Id("id");

        return Disp(Seq(
            Neg, Sp, Call("Surjective", projection), Sp, Land, Esc,
            Call(
                "Refines",
                Compose(identity, projection),
                Compose(oldConcept, projection)),
            Sp, Land, Esc,
            Neg, Sp, Call("Refines", identity, oldConcept), Dot));
    }
}
