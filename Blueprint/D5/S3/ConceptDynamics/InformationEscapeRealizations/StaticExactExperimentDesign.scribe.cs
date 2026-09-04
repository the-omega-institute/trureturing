using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class StaticExactExperimentDesignDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/StaticExactExperimentDesign.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen static exact-design theorem realizes the typed two-CUT law.",
        H("Static Exact Experiment Design Realization"),
        Blocks(
            Node("static-exact-design-realization", "static_exact_design_realization",
                "Legacy realization equivalence",
                Call("LegacyPrimitiveRealization", F.Id("staticExactExperimentArena"),
                    F.Id("StaticExactDesignStatement"),
                    F.Id("staticExactExperimentRealization")),
                "Both directions unfold the concrete experiment response table."),
            Node("static-exact-design-partition-count", "static_exact_design_partition_count",
                "Three kernel classes", Seq(Call("card", F.Id("signatureClasses")), Sp, Eq, Sp, D(3)),
                "The three model indices have three distinct two-bit signatures."),
            Node("static-exact-design-private-pair", "static_exact_design_private_pair",
                "Private pair separation",
                Call("Not", Call("agrees", F.Id("staticExactExperimentRealization"), D(0), D(1))),
                "The change-X readout separates model zero from model one."))));

    private static DocumentBlock.Describe Node(string id, string declaration, string title,
        Formula statement, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(statement, Dot))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))),
            DescribeRole.Theorem);
}
