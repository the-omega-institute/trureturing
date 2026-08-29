using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Postprocessing;

internal sealed class PostprocessingKernelMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Postprocessing/PostprocessingKernelMonotonicity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Postprocessing can only enlarge a readout equality kernel.",
        H("Postprocessing Kernel Monotonicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("postprocessing-only-enlarges-the-equality-kernel"),
            DeclarationHandle.Create(Prefix + "postprocessing_kernel_mono"),
            H("Postprocessing only enlarges the equality kernel"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix an arbitrary readout q and deterministic postprocessing map p.")),
                Paragraph(Text(
                    "Any equality q(x) = q(y) remains an equality after applying p, so every "
                        + "original collision lies in the processed kernel.")),
                Paragraph(Text(
                    "Only non-strict inclusion is claimed; p may preserve the kernel exactly "
                        + "or identify additional source pairs."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Statement()
    {
        Formula q = F.Id("q");
        Formula p = F.Id("p");
        return Disp(Seq(
            Forall, Sp, q, Colon, Sp, Arrow(F.Id("X"), F.Id("Y")), Comma, Sp,
            p, Colon, Sp, Arrow(F.Id("Y"), F.Id("Z")), Comma, Sp,
            Call("ker", q), Sp, Subseteq, Sp,
            Call("ker", Seq(p, Sp, Circ, Sp, q)), Dot));
    }
}
