using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class TransversalFixedPointDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/WorldModel/TransversalFixedPoint.WorldModelDiagram.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One fixed anchor determines a fixed coherent section across semiconjugate world models.",
        H("Transversal Fixed Points Across World Models"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("coherent-section-fixed-from-one-anchor"),
                DeclarationHandle.Create(Prefix + "coherent_section_fixed_from_anchor"),
                H("Fixedness propagates across a coherent section"),
                StatementSource.FromAuthor(SectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A world-model diagram supplies one typed state space and update per "
                            + "model, together with pairwise bridges that semiconjugate the "
                            + "updates.")),
                    Paragraph(Text(
                        "A coherent section chooses one state per model and requires every bridge "
                            + "to carry the source choice to the target choice.")),
                    Paragraph(Text(
                        "If one selected anchor is fixed, semiconjugacy transports fixedness to "
                            + "every other coordinate of the coherent section."))),
                DescribeRole.Theorem))));

    private static Formula SectionFormula() => Disp(Seq(
        Call("Coherent", F.Id("x")), Sp, Land, Sp,
        Call("IsFixedPt", Sub(F.Id("F"), F.Id("i0")),
            Sub(F.Id("x"), F.Id("i0"))), Sp, Rightarrow, Sp,
        Forall, Sp, F.Id("j"), Comma, Sp,
        Call("IsFixedPt", Sub(F.Id("F"), F.Id("j")),
            Sub(F.Id("x"), F.Id("j")))));
}
