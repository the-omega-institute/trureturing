using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Dialectics;

internal sealed class OneStepReadoutRepairDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Dialectics/OneStepReadoutRepair.one_step_readout_repair";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The current and next readouts form their canonical least joint interface.",
        H("One-Step Readout Repair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("one-step-readout-repair"),
                DeclarationHandle.Create(Declaration),
                H("The current and next readouts form the least repair"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source state, readout, and update are independent primitives. "
                            + "Their repaired interface is the canonical concept join of the "
                            + "current readout and its value after one update.")),
                    Paragraph(Text(
                        "The first two public conjuncts retain the current readout and determine "
                            + "the next readout. The final clause quantifies over another "
                            + "interface and its two supplied factor maps.")),
                    Paragraph(Text(
                        "Pairing those supplied maps gives the displayed factorization of the "
                            + "canonical joint readout, which is the coarseness assertion."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula TheoremFormula()
    {
        Formula source = F.Id("X");
        Formula output = F.Id("B");
        Formula comparison = F.Id("C");
        Formula readout = F.Id("q");
        Formula update = F.Id("F");
        Formula other = F.Id("r");
        Formula currentFactor = F.Id("a");
        Formula nextFactor = F.Id("b");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula next = Seq(readout, Sp, Circ, Sp, update);
        Formula repair = Call("conceptJoin", readout, Grp(next));
        Formula pairedFactor = Seq(
            Langle, Sp, currentFactor, Comma, Sp, nextFactor, Sp, Rangle);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, source, Comma, Sp, output, Colon, Sp, type, Comma, Sp,
            readout, Colon, Sp, Arrow(source, output), Comma, Sp,
            update, Colon, Sp, Arrow(source, source), Comma, RowBreak, Grp(),
            Refines(readout, repair), Sp, Land, RowBreak, Grp(),
            Refines(Grp(next), repair), Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, comparison, Colon, Sp, type, Comma, Sp,
            other, Colon, Sp, Arrow(source, comparison), Comma, Sp,
            currentFactor, Comma, Sp, nextFactor, Colon, Sp,
            Arrow(comparison, output), Comma, RowBreak, Grp(),
            readout, Sp, Eq, Sp, currentFactor, Sp, Circ, Sp, other,
            Sp, Rightarrow, Sp,
            next, Sp, Eq, Sp, nextFactor, Sp, Circ, Sp, other,
            Sp, Rightarrow, Sp,
            repair, Sp, Eq, Sp, pairedFactor, Sp, Circ, Sp, other,
            Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
