using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Fusion;

internal sealed class SharpProductCompletionDepthDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/Fusion/SharpProductCompletionDepth."
            + "sharp_product_completion_depth";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp local witnesses give the maximum law for finite product completion depth.",
        H("Sharp Product Completion Depth"),
        Blocks(Describe.Lean(
            DescribeId.Create("sharp-product-completion-depth"),
            DeclarationHandle.Create(Declaration),
            H("The slowest sharp local factor fixes the product completion depth"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A finite index set carries dependent state and output families. The full "
                        + "dependent product of state carriers is finite, and every component "
                        + "state carrier is nonempty so a local witness can be embedded while "
                        + "all other coordinates remain fixed.")),
                Paragraph(Text(
                    "At every positive local depth, the finite word already determines the "
                        + "complete itinerary and a pair agrees through the preceding depth but "
                        + "differs at the stated depth. At local depth zero, equality of the "
                        + "current readout determines the complete itinerary.")),
                Paragraph(Text(
                    "The update and readout on the independent product are constructed "
                        + "pointwise from the component maps. The canonical least observation "
                        + "stability depth of that product is the finite maximum of the local "
                        + "depths.")),
                Paragraph(Text(
                    "The proof applies the existing exact semantics of shortest distance. "
                        + "Every global first mismatch is bounded by its differing coordinate, "
                        + "and every positive sharp local witness embeds as a global pair with "
                        + "the same first mismatch."))),
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
        Formula itineraryFirst = Call("itinerary", update, readout, i, first);
        Formula itinerarySecond = Call("itinerary", update, readout, i, second);

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

        Formula positiveCompletion = Seq(
            Forall, Sp, i, InMacro, Sp, indexType, Comma, Sp,
            D(0), Sp, Lt, Sp, depthAt, Sp, Rightarrow, Sp,
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, stateAt, Comma, Sp,
            Call("word", update, readout, i, depthAt, first), Sp, Eq, Sp,
            Call("word", update, readout, i, depthAt, second), Sp, Rightarrow, Sp,
            itineraryFirst, Sp, Eq, Sp, itinerarySecond);
        Formula sharpWitness = Seq(
            Forall, Sp, i, InMacro, Sp, indexType, Comma, Sp,
            D(0), Sp, Lt, Sp, depthAt, Sp, Rightarrow, Sp,
            Exists, Sp, first, Comma, Sp, second, InMacro, Sp, stateAt, Comma, Sp,
            Call("word", update, readout, i,
                Seq(depthAt, Sp, Minus, Sp, D(1)), first), Sp, Eq, Sp,
            Call("word", update, readout, i,
                Seq(depthAt, Sp, Minus, Sp, D(1)), second), Sp, Land, Sp,
            Call("itineraryAt", update, readout, i, first, depthAt), Sp, Neq, Sp,
            Call("itineraryAt", update, readout, i, second, depthAt));
        Formula zeroCompletion = Seq(
            Forall, Sp, i, InMacro, Sp, indexType, Comma, Sp,
            depthAt, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
            Forall, Sp, first, Comma, Sp, second, InMacro, Sp, stateAt, Comma, Sp,
            Call("q", i, first), Sp, Eq, Sp, Call("q", i, second), Sp,
            Rightarrow, Sp, itineraryFirst, Sp, Eq, Sp, itinerarySecond);
        Formula hypotheses = Seq(
            Call("Fintype", indexType), Sp, Land, Sp,
            Call("Fintype", dependentStateProduct), Sp, Land, Sp,
            Open, Forall, Sp, i, InMacro, Sp, indexType, Comma, Sp,
            Call("Nonempty", stateAt), Close, Sp, Land,
            RowBreak, Grp(),
            Open, positiveCompletion, Close, Sp, Land,
            RowBreak, Grp(),
            Open, sharpWitness, Close, Sp, Land,
            RowBreak, Grp(),
            Open, zeroCompletion, Close);
        Formula conclusion = Seq(
            Call("observationStabilityDepth",
                Call("pointwiseUpdate", update), Call("pointwiseReadout", readout)),
            Sp, Eq, Sp, Call("finiteMax", indexType, localDepth));

        return Disp(Seq(
            Forall, Sp, indexType, Colon, Sp, type, Comma, Sp,
            typedFamilies, Comma,
            RowBreak, Grp(),
            typedUpdate, Comma, Sp, typedReadout, Comma, Sp, typedDepth, Comma,
            RowBreak, Grp(),
            hypotheses, Sp, Rightarrow,
            RowBreak, Grp(),
            conclusion, Dot));
    }
}
