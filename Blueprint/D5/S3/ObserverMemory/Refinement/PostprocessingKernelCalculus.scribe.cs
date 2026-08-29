using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class PostprocessingKernelCalculusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ObserverMemory/Refinement/PostprocessingKernelCalculus.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Postprocessing enlarges readout kernels, with equality exactly on injective realized postprocessing and strictness witnessed by a realized collision.",
        H("Postprocessing Kernel Calculus"),
        Blocks(
            Theorem(
                "postprocessing-kernel-le",
                "postprocessing_kernel_le",
                PostprocessingKernelLeFormula(),
                "Postprocessing Kernel le",
                "Deterministic postprocessing can only enlarge the equality kernel.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "postprocessing-kernel-eq-iff-inj-on-range",
                "postprocessing_kernel_eq_iff_injOn_range",
                PostprocessingKernelEqIffInjonRangeFormula(),
                "Postprocessing Kernel eq iff Inj On Range",
                "Postprocessing preserves exactly the original kernel iff it is injective on values that the original readout actually realizes.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."),
            Theorem(
                "postprocessing-strict-iff-range-collision",
                "postprocessing_strict_iff_range_collision",
                PostprocessingStrictIffRangeCollisionFormula(),
                "Postprocessing Strict iff Range Collision",
                "Kernel growth is strict exactly when two realized readout values are separated before postprocessing and collide afterwards.",
                "The declaration keeps its parameters and hypotheses explicit; the result "
                    + "makes no converse or broader existence claim beyond that scope."))));

    private static DocumentBlock.Describe Theorem(
        string id,
        string declaration,
        Formula statement,
        string title,
        string firstParagraph,
        string secondParagraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(firstParagraph)),
                Paragraph(Text(secondParagraph))),
            DescribeRole.Theorem);

private static Formula PostprocessingKernelLeFormula() => Statement(
    [Typed(Seq(F.Id("X")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Z")), Seq(F.Id("Type"))), Typed(Seq(F.Id("q")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("Y")))), Typed(Seq(F.Id("postprocess")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Z"))))],
        [],
        [],
        Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("q"), Sp, Leq, Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("postprocess"), Sp, Circ, Sp, F.Id("q"), Close));

private static Formula PostprocessingKernelEqIffInjonRangeFormula() => Statement(
    [Typed(Seq(F.Id("X")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Z")), Seq(F.Id("Type"))), Typed(Seq(F.Id("q")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("Y")))), Typed(Seq(F.Id("postprocess")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Z"))))],
        [],
        [],
        Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("postprocess"), Sp, Circ, Sp, F.Id("q"), Close, Sp, Eq, Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("q"), Sp, Leftrightarrow, Sp, F.Id("Set"), Dot, F.Id("InjOn"), Sp, F.Id("postprocess"), Sp, Open, F.Id("Set"), Dot, F.Id("range"), Sp, F.Id("q"), Close));

private static Formula PostprocessingStrictIffRangeCollisionFormula() => Statement(
    [Typed(Seq(F.Id("X")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Y")), Seq(F.Id("Type"))), Typed(Seq(F.Id("Z")), Seq(F.Id("Type"))), Typed(Seq(F.Id("q")), new Formula.TypeArrow(Seq(F.Id("X")), Seq(F.Id("Y")))), Typed(Seq(F.Id("postprocess")), new Formula.TypeArrow(Seq(F.Id("Y")), Seq(F.Id("Z"))))],
        [],
        [],
        Seq(F.Id("Setoid"), Dot, F.Id("ker"), Sp, F.Id("q"), Sp, Lt, Sp, F.Id("Setoid"), Dot, F.Id("ker"), Sp, Open, F.Id("postprocess"), Sp, Circ, Sp, F.Id("q"), Close, Sp, Leftrightarrow, Sp, Exists, Sp, F.Id("x"), Sp, F.Id("y"), Comma, Sp, F.Id("q"), Sp, F.Id("x"), Sp, Neq, Sp, F.Id("q"), Sp, F.Id("y"), Sp, Land, Sp, F.Id("postprocess"), Sp, Open, F.Id("q"), Sp, F.Id("x"), Close, Sp, Eq, Sp, F.Id("postprocess"), Sp, Open, F.Id("q"), Sp, F.Id("y"), Close));

private static Formula Typed(Formula name, Formula type) =>
    Seq(name, Colon, Sp, type);

private static Formula Statement(
    Formula[] binders,
    Formula[] constraints,
    Formula[] hypotheses,
    Formula conclusion)
{
    List<Formula> items = [];
    if (binders.Length > 0)
    {
        items.Add(Forall);
        items.Add(Sp);
    }
    for (int index = 0; index < binders.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(binders[index]);
    }
    foreach (Formula constraint in constraints)
    {
        if (binders.Length > 0 || constraint != constraints[0])
        {
            items.Add(Comma);
            items.Add(Sp);
        }
        items.Add(constraint);
    }
    if (binders.Length > 0 || constraints.Length > 0)
    {
        items.Add(Comma);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    for (int index = 0; index < hypotheses.Length; index++)
    {
        if (index > 0)
        {
            items.Add(Sp);
            items.Add(Land);
            items.Add(Sp);
        }
        items.Add(Seq(Open, hypotheses[index], Close));
    }
    if (hypotheses.Length > 0)
    {
        items.Add(Sp);
        items.Add(Rightarrow);
        items.Add(RowBreak);
        items.Add(Grp());
    }
    items.Add(Seq(Open, conclusion, Close));
    items.Add(Dot);
    return Disp(Seq([.. items]));
}
}
