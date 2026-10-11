using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class ComplexColimitDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact colimits of arbitrary unbounded complexes. These new proofs are used to assemble weak equivalences in the cellular localization argument. Released under the Apache 2.0 license.",
        H("Complex Colimit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-complexcolimit-complexdiagramcolimitiso-naturality"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ComplexColimit.complexDiagramColimitIso_naturality"),
                H("complex Diagram Colimit Iso naturality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Exact colimits of arbitrary unbounded complexes. These new proofs are used to assemble weak equivalences in the cellular localization argument. Released under the Apache 2.0 license."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-complexcolimit-quasiiso-colimitmap"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/ComplexColimit.quasiIso_colimitMap"),
                H("quasi Iso colimit Map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exact colimits preserve all quasi-isomorphisms of arbitrary unbounded diagrams. In particular, this covers filtered colimits and arbitrary sums in the protected light condensed category."))),
                DescribeRole.Theorem))));
}
