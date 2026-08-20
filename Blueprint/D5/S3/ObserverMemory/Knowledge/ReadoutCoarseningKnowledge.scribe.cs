using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Knowledge;

internal sealed class ReadoutCoarseningKnowledgeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coarsening a readout contravariantly shrinks its complex knowledge space.",
        H("Readout Coarsening and Knowledge"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("readout-coarsening-shrinks-knowledge"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/Knowledge/ReadoutCoarseningKnowledge."
                        + "readout_coarsening_shrinks_knowledge"),
                H("Readout coarsening shrinks knowledge"),
                StatementSource.FromAuthor(CoarseningFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a readout q on a world type X, the imported knowledge space is the "
                            + "range of the linear pullback from complex observables on realized "
                            + "readout classes. It therefore constructs the source set of complex "
                            + "functions that factor through q.")),
                    Paragraph(Text(
                        "The exact repository membership theorem identifies that pullback range "
                            + "with Mathlib's FactorsThrough predicate. If q1 is forget composed "
                            + "with q0, equality on a q0 fiber implies equality on the corresponding "
                            + "q1 fiber, so every q1-known observable is q0-known.")),
                    Paragraph(Text(
                        "The proof applies mem_knowledgeSpace_iff_factorsThrough in both directions. "
                            + "Repository and pinned-Mathlib searches also checked the timed same-"
                            + "codomain knowledge theorem, factorsThrough_iff, extend_comp, comp_left, "
                            + "and comp_right; none directly states the displayed general inclusion."))),
                DescribeRole.Theorem))));

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula CoarseningFormula()
    {
        Formula x = F.Id("X");
        Formula yZero = Subscript(F.Id("Y"), D(0));
        Formula yOne = Subscript(F.Id("Y"), D(1));
        Formula qZero = Subscript(F.Id("q"), D(0));
        Formula qOne = Subscript(F.Id("q"), D(1));
        Formula forget = F.Id("r");
        Formula knowledge = F.Id("K");

        return Disp(Seq(
            Forall, Sp, x, Comma, Sp, yZero, Comma, Sp, yOne, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Esc,
            qZero, Colon, Sp, x, Sp, To, Sp, yZero, Comma, Sp,
            qOne, Colon, Sp, x, Sp, To, Sp, yOne, Comma, Esc,
            forget, Colon, Sp, yZero, Sp, To, Sp, yOne, Comma, Esc,
            qOne, Sp, Eq, Sp, forget, Sp, Circ, Sp, qZero, Sp, Rightarrow, Esc,
            Apply(knowledge, qOne), Sp, Subseteq, Sp,
            Apply(knowledge, qZero), Dot));
    }
}
