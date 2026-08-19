using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class CascadeCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fine completion followed by coarse completion is direct coarse completion.",
        H("Cascade Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fine-completion-followed-by-coarse-completion"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Refinement/CascadeCompletion."
                        + "cascade_completion"),
                H("The completion cascade identifies with direct coarse completion"),
                StatementSource.FromAuthor(CascadeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the coarse readout be obtained by applying a forgetful map to the "
                            + "fine readout. On the fine predictive completion, compose the "
                            + "current readout with that same map. Equality of every future "
                            + "coarse readout then agrees exactly with equality of the original "
                            + "coarse itineraries on projected states.")),
                    Paragraph(Text(
                        "The canonical factor from the fine completion to the coarse completion "
                            + "is surjective. Its kernel is precisely the second-stage future "
                            + "relation, so quotienting the fine completion by that relation "
                            + "gives the direct coarse completion.")),
                    Paragraph(Text(
                        "The quotient equivalence is the pinned Mathlib third isomorphism "
                            + "theorem for setoids. Its value on every second-stage class is "
                            + "the canonical factor, and on an original projected state it is "
                            + "the coarse completion projection.")),
                    Paragraph(Text(
                        "Repository search found the exact completion factor theorem and the "
                            + "complete-itinerary construction. Pinned Mathlib and Loogle found "
                            + "Setoid.quotientQuotientEquivQuotient, Quotient.map_surjective, "
                            + "Quotient.eq, and Quotient.congrRight; each is applied in the "
                            + "Lean bridge. LeanSearch returned HTTP 404 and no usable result."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Apply2(Formula function, Formula first, Formula second) =>
        Apply(Apply(function, first), second);

    private static Formula QuotientOf(Formula relation) =>
        Seq(Operatorname, Grp(F.Id("Quotient")), Open, relation, Close);

    private static Formula CascadeFormula()
    {
        Formula tau = F.Id("tau");
        Formula q = F.Id("q");
        Formula r = F.Id("r");
        Formula h = F.Id("h");
        Formula y = F.Id("y");
        Formula yPrime = F.Id("yPrime");
        Formula state = F.Id("state");
        Formula piQ = F.Id("piQ");
        Formula piR = F.Id("piR");
        Formula kappa = F.Id("kappa");
        Formula equivalence = F.Id("e");
        Formula zQ = F.Id("Zq");
        Formula zR = F.Id("Zr");
        Formula secondRelation = Call("secondStageRelation", tau, q, h);
        Formula coarseRelation = Call("ker", Call("completeItinerary", tau, r));
        Formula projectedRelation = Call(
            "secondStageRelation", tau, q, h);
        Formula projectedLeft = Apply(piQ, y);
        Formula projectedRight = Apply(piQ, yPrime);
        Formula quotientClass = Apply(F.Id("mk"), state);
        Formula projectedClass = Apply(F.Id("mk"), projectedLeft);

        return Disp(Seq(
            Forall, Sp, tau, Comma, Sp, q, Comma, Sp, r, Comma, Sp, h, Comma, Esc,
            r, Sp, Eq, Sp, h, Sp, Circ, Sp, q, Sp, Rightarrow, Sp,
            Open, Forall, Sp, y, Comma, Sp, yPrime, Comma, Esc,
            Apply2(projectedRelation, projectedLeft, projectedRight), Sp, Iff, Sp,
            Call("ker", Call("completeItinerary", tau, r)), Open, y, Comma, Sp, yPrime,
            Close, Sp, Land, Esc,
            Call("Surjective", kappa), Sp, Land, Esc,
            secondRelation, Sp, Eq, Sp, Call("ker", kappa), Sp, Land, Esc,
            Exists, Sp, equivalence, Colon, Sp,
            QuotientOf(secondRelation), Sp, Equiv, Sp, zR, Comma, Esc,
            Open, Forall, Sp, state, Comma, Esc,
            Apply(equivalence, quotientClass), Sp, Eq, Sp,
            Apply(kappa, state), Close, Sp, Land, Esc,
            Forall, Sp, y, Comma, Esc,
            Apply(equivalence, projectedClass), Sp, Eq, Sp, Apply(piR, y), Dot));
    }
}
