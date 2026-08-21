using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Fusion;

internal sealed class IndependentProductCompletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent product readouts have a product predictive completion and componentwise quotient dynamics.",
        H("Independent Product Completion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("independent-product-completion"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Fusion/IndependentProductCompletion."
                        + "independent_product_completion"),
                H("Independent product completion is a product with component dynamics"),
                StatementSource.FromAuthor(IndependentFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For component state spaces with self-maps tau1 and tau2 and readouts q1 "
                            + "and q2, the product state update and paired readout are constructed "
                            + "pointwise. Each predictive completion is the quotient by equality of "
                            + "all future readout values.")),
                    Paragraph(Text(
                        "The public equivalence sends a product quotient class to the pair of its "
                            + "component quotient classes. Coordinate equality of complete itineraries "
                            + "makes this map well-defined; representatives of either component give "
                            + "surjectivity, and the two coordinate quotient equalities give injectivity.")),
                    Paragraph(Text(
                        "The induced update on the product quotient is carried by this equivalence to "
                            + "the pair of the two component quotient updates, which is the source's "
                            + "independent direct-product dynamics.")),
                    Paragraph(Text(
                        "Pinned repository hits CompletedState, completionProjection, completionUpdate, "
                            + "and completeItinerary are imported and applied directly. Quotient lift, "
                            + "soundness, exactness, and Equiv.ofBijective are the pinned primitives; "
                            + "no exact independent-product completion theorem was found."))),
                DescribeRole.Theorem))));

    private static Formula IndependentFormula()
    {
        Formula tau1 = F.Id("tau1");
        Formula tau2 = F.Id("tau2");
        Formula q1 = F.Id("q1");
        Formula q2 = F.Id("q2");
        Formula productState = Call("CompletedState",
            Call("productUpdate", tau1, tau2), Call("productReadout", q1, q2));
        Formula componentState = Call("CompletedState", tau1, q1);
        Formula otherComponentState = Call("CompletedState", tau2, q2);
        Formula state = F.Id("state");
        Formula image = Call("productCompletionMap", tau1, tau2, q1, q2, state);
        Formula updateProduct = Call("completionUpdate",
            Call("productUpdate", tau1, tau2), Call("productReadout", q1, q2), state);
        Formula updateFirst = Call("completionUpdate", tau1, q1,
            Call("first", image));
        Formula updateSecond = Call("completionUpdate", tau2, q2,
            Call("second", image));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, tau1, Comma, Sp, tau2, Comma, Sp, q1, Comma, Sp, q2, Comma, RowBreak,
            Operatorname, Grp(F.Id("Nonempty")), Open, productState, Equiv, Sp,
            Open, componentState, Close, Times, Open, otherComponentState, Close, Close,
            Sp, Land, RowBreak,
            Forall, Sp, state, Colon, Sp, productState, Comma, RowBreak,
            Call("productCompletionMap", tau1, tau2, q1, q2, updateProduct), Sp, Eq, Sp,
            Open, updateFirst, Comma, Sp, updateSecond, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
