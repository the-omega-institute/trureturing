using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class InverseLimitEventTotalVariationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full event distance between two finite laws on a finite-alphabet inverse limit "
            + "is the supremum of the distances between their actual level projections.",
        H("Total Variation on Compatible Threads"),
        Blocks(Describe.Lean(
            DescribeId.Create("total-variation-equals-level-supremum"),
            DeclarationHandle.Create(
                "D5/S3/Estimation/DataProcessing/InverseLimitEventTotalVariation."
                    + "total_variation_eq_iSup_level"),
            H("All measurable events are controlled by level laws"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A thread is a sequence whose adjacent coordinates obey the prescribed "
                        + "bonding maps. The sample space consists of a fixed finite tuple of "
                        + "threads. A level projection reads that same level at every node.")),
                Paragraph(Text(
                    "Every alphabet is finite and every singleton is measurable. Both measures "
                        + "are finite. The statement allows arbitrary bonding maps, arbitrary "
                        + "tuple length, zero-mass labels, and laws without feasibility constraints.")),
                Paragraph(Text(
                    "The inherited measurable structure is the Borel structure when the alphabets "
                        + "carry their discrete topologies. Total variation takes the supremum "
                        + "over all measurable events of the maximum of the two directed "
                        + "truncated measure differences.")),
                Paragraph(Text(
                    "Compatibility lifts two cylinder events to a common higher level. These "
                        + "events form a ring that generates the entire measurable structure. "
                        + "Approximation in the sum of the two measures then transfers the "
                        + "cylinder bound to every measurable event.")),
                Paragraph(Text(
                    "This identity compares two given laws. It does not select a compatible "
                        + "family from separate finite feasible sets or assert that a nearest "
                        + "feasible law exists."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula x = F.Id("X");
        Formula p = F.Id("P");
        Formula q = F.Id("Q");
        Formula l = F.Id("l");
        Formula projection = new Formula.Subscript(F.Id("pi"), l);
        Formula finiteMeasures = Call("FiniteMeasures", x);
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, p, Comma, Sp, q, Sp, InMacro, Sp, finiteMeasures, Comma),
            Seq(Call("TV", p, q), Sp, Eq, Sp,
                Operatorname, Grp(F.Id("sup")), Underscore,
                Grp(l, Sp, InMacro, Sp, natural), Sp,
                Call("TV", Call("push", projection, p), Call("push", projection, q))),
        ]));
    }
}
