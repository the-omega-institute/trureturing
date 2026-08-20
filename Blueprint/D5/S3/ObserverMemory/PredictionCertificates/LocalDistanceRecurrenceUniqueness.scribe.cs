using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionCertificates;

internal sealed class LocalDistanceRecurrenceUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The local readout recurrence uniquely fixes the shortest distinguishing distance.",
        H("Local Distance Recurrence Uniqueness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-recurrence-uniquely-fixes-shortest-distance"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionCertificates/"
                        + "LocalDistanceRecurrenceUniqueness."
                        + "local_recurrence_uniquely_determines_shortest_distance"),
                H("The local recurrence uniquely fixes shortest distance"),
                StatementSource.FromAuthor(UniquenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Represent an extended natural number by Option Nat, with none denoting "
                            + "infinity. A current readout mismatch forces distance zero. When "
                            + "the readouts agree, the distance is the successor of the next-pair "
                            + "distance, with successor preserving infinity.")),
                    Paragraph(Text(
                        "The canonical table is constructed from the least future time at which "
                            + "the two readouts differ, and is infinite when no such time exists. "
                            + "Thus the source object is defined by first mismatch, independently "
                            + "of the equality proved here.")),
                    Paragraph(Text(
                        "The exact repository theorem local_distance_eq_shortest already proves "
                            + "the full statement and is applied directly. Pinned Mathlib grep "
                            + "found no equal first-mismatch recurrence theorem."))),
                DescribeRole.Theorem))));

    private static Formula Typed(string name, Formula type) =>
        Seq(F.Id(name), Colon, Sp, type);

    private static Formula UniquenessFormula()
    {
        Formula stateType = F.Id("Y");
        Formula outputType = F.Id("O");
        Formula step = F.Id("tau");
        Formula readout = F.Id("q");
        Formula distance = F.Id("delta");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula extendedNaturals = Call("Option", naturals);
        Formula distanceType = new Formula.TypeArrow(
            stateType, new Formula.TypeArrow(stateType, extendedNaturals));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, outputType, Comma, RowBreak,
            Typed("tau", new Formula.TypeArrow(stateType, stateType)), Comma, Sp,
            Typed("q", new Formula.TypeArrow(stateType, outputType)), Comma, RowBreak,
            Typed("delta", distanceType), Comma, RowBreak,
            Call("LocalDistanceChecks", step, readout, distance), Sp, Rightarrow, RowBreak,
            distance, Sp, Eq, Sp, Call("shortestDistance", step, readout), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
