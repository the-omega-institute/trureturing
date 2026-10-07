using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class RealizedAdjunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. The genuine unbounded adjunction into the protected D(Solid), obtained from the proved realization equivalence and the actual local reflector. The right adjoint is exactly the protected derivedInclusion.",
        H("Realized Adjunction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-realizedadjunction-realizedderivedsolidification"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/RealizedAdjunction.realizedDerivedSolidification"),
                H("realized Derived Solidification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Copyright (c) 2026. Released under the Apache 2.0 license. The genuine unbounded adjunction into the protected D(Solid), obtained from the proved realization equivalence and the actual local reflector. The right adjoint is exactly the protected derivedInclusion."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-realizedadjunction-realizedderivedsolidificationadjunction"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/RealizedAdjunction.realizedDerivedSolidificationAdjunction"),
                H("realized Derived Solidification Adjunction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual adjunction has no existence, realization or full-faithfulness premise. Its equivalence is constructed by the unbounded resolution proof."))),
                DescribeRole.Definition))));
}
