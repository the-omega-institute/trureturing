using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Fusion;

internal sealed class ProductCompletionDepthUpperBoundDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/Fusion/ProductCompletionDepthUpperBound."
            + "product_completion_depth_upper_bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The maximum local completion depth completes a pointwise product observer.",
        H("Product Completion Depth Upper Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("product-completion-depth-upper-bound"),
            DeclarationHandle.Create(Declaration),
            H("The slowest local completion depth suffices for the product"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite index type carries dependent state and output families, with "
                        + "one update, readout, and completion depth at every coordinate.")),
                Paragraph(Text(
                    "The sole semantic premise says that each local word through its stated "
                        + "depth determines that factor's complete itinerary. No sharp witness, "
                        + "least-depth assumption, or nonemptiness premise is required.")),
                Paragraph(Text(
                    "The global update and readout are the pointwise products of the local maps. "
                        + "Equality of their word through the finite maximum restricts to equality "
                        + "of every local word, so the local completion laws give equality of the "
                        + "complete product itineraries.")),
                Paragraph(Text(
                    "Repository primitives futureReadoutWord and completeItinerary are used "
                        + "directly. The sharper product-depth equality theorem is not applied "
                        + "because its witness premises are absent from this upper-bound claim."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateFamily = F.Id("Y");
        Formula outputFamily = F.Id("O");
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula localDepth = F.Id("m");
        Formula i = F.Id("i");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula stateAt = Call("Y", i);
        Formula outputAt = Call("O", i);
        Formula depthAt = Call("m", i);
        Formula dependentStateProduct = Seq(
            Prod, Underscore, Grp(i, Sp, InMacro, Sp, indexType), Sp, stateAt);
        Formula pointwiseUpdate = Call("pointwiseUpdate", update);
        Formula pointwiseReadout = Call("pointwiseReadout", readout);
        Formula maximum = Call("finiteMax", indexType, localDepth);

        Formula typedFamilies = Seq(
            stateFamily, Comma, Sp, outputFamily, Colon, Sp,
            indexType, Sp, To, Sp, type);
        Formula typedUpdate = Seq(
            update, Colon, Sp, Forall, Sp, i, InMacro, Sp, indexType, Comma, Sp,
            stateAt, Sp, To, Sp, stateAt);
        Formula typedReadout = Seq(
            readout, Colon, Sp, Forall, Sp, i, InMacro, Sp, indexType, Comma, Sp,
            stateAt, Sp, To, Sp, outputAt);
        Formula typedDepth = Seq(
            localDepth, Colon, Sp, indexType, Sp, To, Sp, naturals);

        Formula localCompletion = Seq(
            Forall, Sp, i, InMacro, Sp, indexType, Comma, Sp,
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, stateAt, Comma, Sp,
            Call("word", update, readout, i, depthAt, first), Sp, Eq, Sp,
            Call("word", update, readout, i, depthAt, second), Sp, Rightarrow, Sp,
            Call("itinerary", update, readout, i, first), Sp, Eq, Sp,
            Call("itinerary", update, readout, i, second));
        Formula globalCompletion = Seq(
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp,
            dependentStateProduct, Comma, Sp,
            Call("word", pointwiseUpdate, pointwiseReadout, maximum, first),
            Sp, Eq, Sp,
            Call("word", pointwiseUpdate, pointwiseReadout, maximum, second),
            Sp, Rightarrow, Sp,
            Call("itinerary", pointwiseUpdate, pointwiseReadout, first),
            Sp, Eq, Sp,
            Call("itinerary", pointwiseUpdate, pointwiseReadout, second));

        return Disp(Seq(
            Forall, Sp, indexType, Colon, Sp, type, Comma, Sp,
            typedFamilies, Comma,
            RowBreak, Grp(),
            typedUpdate, Comma, Sp, typedReadout, Comma, Sp, typedDepth, Comma,
            RowBreak, Grp(),
            Call("Fintype", indexType), Sp, Land, Sp,
            Open, localCompletion, Close, Sp, Rightarrow,
            RowBreak, Grp(),
            globalCompletion, Dot));
    }
}
