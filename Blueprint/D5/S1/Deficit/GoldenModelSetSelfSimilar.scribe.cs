using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class GoldenModelSetSelfSimilarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden conjugate window has unit volume, and the golden beta range splits into "
            + "two disjoint self-similar branches.",
        H("Golden Model-Set Self-Similarity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-conjugate-window-has-unit-volume"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/GoldenModelSetSelfSimilar.golden_window_volume"),
                H("The golden conjugate window has unit volume"),
                StatementSource.FromAuthor(WindowVolumeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The golden window is the closed real interval from minus the inverse "
                            + "square of the golden ratio to the inverse golden ratio. Its Lebesgue "
                            + "volume is the difference of these endpoints, namely the sum of the "
                            + "two inverse powers.")),
                    Paragraph(Text(
                        "The inverse-golden recurrence identifies that sum with one, so the "
                            + "closed conjugate window has length and volume exactly one."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("golden-beta-range-is-self-similar"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/GoldenModelSetSelfSimilar.golden_model_set_self_similar"),
                H("The golden beta range is a disjoint self-similar union"),
                StatementSource.FromAuthor(SelfSimilarityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write B for the range of the exact GoldenInt-valued beta reading. Every "
                            + "canonical digit string belongs to exactly one of two branches: a "
                            + "zero least digit exposes a one-place shift and contributes phi B, "
                            + "while a one least digit forces the next digit to vanish and contributes "
                            + "phi squared plus phi squared B.")),
                    Paragraph(Text(
                        "Conversely, shifting a canonical string by one place and prefixing a "
                            + "canonical one-zero pair both preserve admissibility, so both branches "
                            + "lie in B. Their least digits differ, and uniqueness of canonical golden "
                            + "digits makes the two images disjoint. Thus B is exactly their disjoint union."))),
                DescribeRole.Theorem))));

    private static Formula WindowVolumeFormula() =>
        FormulaDsl.Disp(Equal(Call("volume", Id("goldenWindow")), Num(1)));

    private static Formula SelfSimilarityFormula()
    {
        Formula firstBranch = Id("phiBranch");
        Formula secondBranch = Id("phiSquaredBranch");
        Formula union = Call("union", firstBranch, secondBranch);

        return FormulaDsl.Disp(new Formula.Logic(
            Equal(Id("goldenModelSet"), union),
            FormulaLogicOperator.And,
            Call("Disjoint", firstBranch, secondBranch)));
    }
}
