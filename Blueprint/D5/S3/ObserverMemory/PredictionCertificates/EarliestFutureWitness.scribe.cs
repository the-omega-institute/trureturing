using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionCertificates;

internal sealed class EarliestFutureWitnessDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ObserverMemory/PredictionCertificates/EarliestFutureWitness."
            + "memory_is_earliest_future_witness";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Memory is the earliest future distinction of states merged by the current readout.",
        H("Earliest Future Witness"),
        Blocks(Describe.Lean(
            DescribeId.Create("memory-is-earliest-future-witness"),
            DeclarationHandle.Create(Declaration),
            H("Canonical memory records the first future mismatch"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Assume two states have the same current readout. Their canonical finite "
                        + "shortest distance is some positive depth exactly when their future "
                        + "readouts differ at that depth and agree at every earlier depth.")),
                Paragraph(Text(
                    "Thus the stored distinction is selected by the first future mismatch, "
                        + "rather than by an arbitrary record of the past. The theorem places "
                        + "no finiteness assumption on the state or readout carrier."))),
            DescribeRole.Theorem))));

    private static Formula Itinerary(Formula state, Formula depth) =>
        Call("I", state, depth);

    private static Formula TheoremFormula()
    {
        Formula update = F.Id("F");
        Formula readout = F.Id("q");
        Formula first = F.Id("x");
        Formula second = F.Id("y");
        Formula depth = F.Id("n");
        Formula earlier = F.Id("m");
        Formula stateType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));

        Formula currentEquality = Seq(
            Call("q", first), Sp, Eq, Sp, Call("q", second));
        Formula distance = Call("shortestDistance", update, readout, first, second);
        Formula earliest = Seq(
            D(0), Sp, Lt, Sp, depth, Sp, Land, Sp,
            Itinerary(first, depth), Sp, Neq, Sp, Itinerary(second, depth), Sp,
            Land,
            RowBreak, Grp(),
            Forall, Sp, earlier, Sp, Lt, Sp, depth, Comma, Sp,
            Itinerary(first, earlier), Sp, Eq, Sp, Itinerary(second, earlier));

        return Disp(Seq(
            Forall, Sp, stateType, Comma, Sp, outputType, Colon, Sp, type,
            Comma, Sp, update, Colon, Sp, stateType, Sp, To, Sp, stateType,
            Comma, Sp, readout, Colon, Sp, stateType, Sp, To, Sp, outputType,
            Comma,
            RowBreak, Grp(),
            first, Comma, Sp, second, Sp, InMacro, Sp, stateType,
            Comma, Sp, depth, Sp, InMacro, Sp, naturals, Comma,
            RowBreak, Grp(),
            currentEquality, Sp, Rightarrow, Sp,
            Open,
            distance, Sp, Eq, Sp, Call("some", depth), Sp, Iff, Sp,
            Open, earliest, Close,
            Close, Dot));
    }
}
