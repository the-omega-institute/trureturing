using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class StrictRefinementBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite state space bounds the number of strict concept refinements.",
        H("Finite Strict Refinement Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-refinement-steps-le-card-sub-initial-image"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/StrictRefinementBound."
                        + "strict_refinement_steps_le_card_sub_initial_image"),
                H("Strict refinements terminate within the cardinality deficit"),
                StatementSource.FromAuthor(BoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A concept readout identifies two states when their coordinates agree. "
                            + "A strict refinement preserves every distinction made by the coarse "
                            + "readout and splits at least one of its equivalence classes.")),
                    Paragraph(Text(
                        "For finite X, each strict step therefore increases the cardinality of the "
                            + "readout image by at least one. The final image injects into X through "
                            + "representatives, so its cardinality is at most the cardinality of X.")),
                    Paragraph(Text(
                        "Combining growth over all steps with the final image bound gives exactly "
                            + "the number of states minus the initial image size. A constant Boolean "
                            + "readout refined by the identity supplies a machine-checked nonempty model."))),
                DescribeRole.Theorem))));

    private static Formula Card(Formula value) =>
        Seq(Lvert, value, Rvert);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula BoundFormula()
    {
        Formula source = F.Id("X");
        Formula coordinate = F.Id("B");
        Formula steps = F.Id("s");
        Formula index = F.Id("i");
        Formula readout = F.Id("C");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula readoutAtI = Subscript(readout, index);
        Formula readoutAtSucc = Subscript(readout, Seq(index, Plus, D(1)));
        Formula initialReadout = Subscript(readout, D(0));
        Formula initialImage = Seq(
            Operatorname, Grp(F.Id("range")), Open, initialReadout, Close);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coordinate, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("Finite")), Sp, source, CloseBracket,
            Comma, Esc,
            steps, InMacro, Sp, naturals, Comma, Sp,
            readout, Colon, Sp,
            Operatorname, Grp(F.Id("Fin")), Open, steps, Plus, D(1), Close,
            Sp, To, Sp, Open, source, Sp, To, Sp, coordinate, Close, Comma, RowBreak,
            Open, Forall, Sp, index, Colon, Sp,
            Operatorname, Grp(F.Id("Fin")), Open, steps, Close, Comma, Sp,
            Call("StrictlyRefines", readoutAtI, readoutAtSucc), Close,
            Sp, Rightarrow, RowBreak,
            steps, Sp, Leq, Sp, Card(source), Sp, Minus, Sp, Card(initialImage), Dot));
    }
}
