using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DefinitionEscape;

internal sealed class BlindKernelReductionMeasureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive weight detects blind residual pairs separated by a new definition.",
        H("Blind Kernel Reduction Measure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("blind-kernel-reduction-measure"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DefinitionEscape/BlindKernelReductionMeasure."
                        + "blind_kernel_reduction_measure"),
                H("Positive reduction weight detects a separated blind pair"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The imported blindResidual is used unchanged. For a proposed definition "
                            + "d, the measured reduction set is its intersection with the "
                            + "complement of the Setoid equality kernel of d. Thus the Lean "
                            + "definition is exactly the displayed P_Gamma formula and introduces "
                            + "no second residual or kernel.")),
                    Paragraph(Text(
                        "The public hypotheses require the abstract real-valued set weight to be "
                            + "nonnegative and to be positive exactly on nonempty sets. Both "
                            + "requirements occur in the theorem type. The conclusion packages "
                            + "the defining equality, nonnegativity, and the equivalence between "
                            + "positive reduction weight and a blind residual pair separated by d.")),
                    Paragraph(Text(
                        "Finite counting weight on Boolean state pairs supplies the positive "
                            + "example. A constant definition supplies the reverse example, and a "
                            + "zero weight shows that nonnegativity without strict nonempty-set "
                            + "detection is insufficient.")),
                    Paragraph(Text(
                        "The closing catalog, language-closure, and target-usefulness maxim is not "
                            + "asserted as a Lean proposition: the source supplies no formal "
                            + "catalog, closure, or usefulness predicates from which a faithful "
                            + "statement could be formed."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Projection(Formula pair, byte index) =>
        Seq(pair, Underscore, Grp(D(index)));

    private static Formula TheoremFormula()
    {
        Formula set = F.Id("S");
        Formula baseline = F.Id("q");
        Formula target = F.Id("T");
        Formula definition = F.Id("d");
        Formula pair = F.Id("p");
        Formula residual = Call("blindResidual", Gamma, baseline, target);
        Formula removed = Call(
            "intersection", residual, Call("complement", Call("ker", definition)));
        Formula reduction = Call(
            "blindKernelReductionMeasure", Nu, Gamma, baseline, target, definition);
        Formula separated = Seq(
            Exists, Sp, pair, Comma, Sp, pair, Sp, InMacro, Sp, residual, Sp, Land, Sp,
            Apply(definition, Projection(pair, 1)), Sp, Neq, Sp,
            Apply(definition, Projection(pair, 2)));
        Formula weightPremises = Seq(
            Open, Forall, Sp, set, Comma, Esc,
            D(0), Sp, Leq, Sp, Apply(Nu, set), Close, Sp, Land, Sp,
            Open, Forall, Sp, set, Comma, Esc,
            D(0), Sp, Lt, Sp, Apply(Nu, set), Sp, Iff, Sp,
            Call("Nonempty", set), Close);

        return Disp(Seq(
            weightPremises, Sp, Rightarrow, RowBreak, Grp(),
            Open, reduction, Sp, Eq, Sp, Apply(Nu, removed), Close, Sp, Land, Sp,
            Open, D(0), Sp, Leq, Sp, reduction, Close, Sp, Land, RowBreak, Grp(),
            Open, D(0), Sp, Lt, Sp, reduction, Sp, Iff, Sp, separated, Close, Dot));
    }
}
