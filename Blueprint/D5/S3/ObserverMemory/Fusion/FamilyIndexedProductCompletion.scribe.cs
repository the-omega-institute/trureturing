using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Fusion;

internal sealed class FamilyIndexedProductCompletionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/Fusion/FamilyIndexedProductCompletion."
            + "family_indexed_product_completion";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite independent readouts have a product completion and pointwise dynamics.",
        H("Family-Indexed Product Completion"),
        Blocks(Describe.Lean(
            DescribeId.Create("family-indexed-product-completion"),
            DeclarationHandle.Create(Declaration),
            H("The predictive completion of a finite product is the product of the completions"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite index type carries dependent state and output families. The global "
                        + "update and readout are constructed pointwise from the component maps, "
                        + "and CompletedState is the canonical quotient by equality of complete "
                        + "future readout itineraries.")),
                Paragraph(Text(
                    "The named canonical equivalence sends the class of a configuration to the "
                        + "family of its coordinate classes. The first public law records this "
                        + "projection computation directly.")),
                Paragraph(Text(
                    "The second public law says that applying the induced global update before "
                        + "the equivalence is exactly the family of component completion updates.")),
                Paragraph(Text(
                    "Pinned repository primitives CompletedState, completionProjection, "
                        + "completionUpdate, and completeItinerary are imported and applied. "
                        + "Pinned Mathlib's exact Setoid.piQuotientEquiv is composed with "
                        + "Quotient.congrRight; no family-indexed repository theorem was found."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Typeclass(string name, Formula type) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, type, Close, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateFamily = F.Id("Y");
        Formula outputFamily = F.Id("O");
        Formula update = F.Id("tau");
        Formula readout = F.Id("q");
        Formula index = F.Id("i");
        Formula configuration = F.Id("y");
        Formula state = F.Id("z");
        Formula equivalence = F.Id("e");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateAt = Call("Y", index);
        Formula outputAt = Call("O", index);
        Formula componentUpdate = Call("tau", index);
        Formula componentReadout = Call("q", index);
        Formula pointwiseUpdate = Call("pointwiseUpdate", update);
        Formula pointwiseReadout = Call("pointwiseReadout", readout);
        Formula productState = Call(
            "CompletedState", pointwiseUpdate, pointwiseReadout);
        Formula componentState = Call(
            "CompletedState", componentUpdate, componentReadout);
        Formula stateProduct = Seq(
            Prod, Underscore, Grp(index, Sp, InMacro, Sp, indexType), Sp, stateAt);
        Formula completionProduct = Seq(
            Prod, Underscore, Grp(index, Sp, InMacro, Sp, indexType), Sp,
            componentState);
        Formula canonicalEquivalence = Call(
            "familyProductCompletionEquiv", update, readout);
        Formula projectedConfiguration = Call(
            "completionProjection", pointwiseUpdate, pointwiseReadout, configuration);
        Formula projectedCoordinates = Seq(
            Open, index, Sp, Mapsto, Sp,
            Call("completionProjection", componentUpdate, componentReadout,
                Apply(configuration, index)), Close);
        Formula updatedProductState = Call(
            "completionUpdate", pointwiseUpdate, pointwiseReadout, state);
        Formula updatedCoordinates = Seq(
            Open, index, Sp, Mapsto, Sp,
            Call("completionUpdate", componentUpdate, componentReadout,
                Apply(Apply(equivalence, state), index)), Close);

        Formula typedUpdate = Seq(
            update, Colon, Sp, Forall, Sp, index, InMacro, Sp, indexType,
            Comma, Sp, stateAt, Sp, To, Sp, stateAt);
        Formula typedReadout = Seq(
            readout, Colon, Sp, Forall, Sp, index, InMacro, Sp, indexType,
            Comma, Sp, stateAt, Sp, To, Sp, outputAt);
        Formula letEquivalence = Seq(
            Operatorname, Grp(F.Id("let")), Open, equivalence, Sp, Eq, Sp,
            canonicalEquivalence, Colon, Sp, productState, Sp, Equiv, Sp,
            completionProduct, Close);
        Formula projectionLaw = Seq(
            Forall, Sp, configuration, Colon, Sp, stateProduct, Comma, Sp,
            Apply(equivalence, projectedConfiguration), Sp, Eq, Sp,
            projectedCoordinates);
        Formula updateLaw = Seq(
            Forall, Sp, state, Colon, Sp, productState, Comma, Sp,
            Apply(equivalence, updatedProductState), Sp, Eq, Sp,
            updatedCoordinates);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, indexType, Colon, Sp, type, Comma, Sp,
            Typeclass("Fintype", indexType), Comma, RowBreak, Grp(),
            stateFamily, Comma, Sp, outputFamily, Colon, Sp,
            indexType, Sp, To, Sp, type, Comma, RowBreak, Grp(),
            typedUpdate, Comma, Sp, typedReadout, Comma, RowBreak, Grp(),
            letEquivalence, Comma, RowBreak, Grp(),
            Open, projectionLaw, Close, Sp, Land, RowBreak, Grp(),
            Open, updateLaw, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
