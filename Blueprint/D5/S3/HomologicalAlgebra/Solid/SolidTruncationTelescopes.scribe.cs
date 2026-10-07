using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class SolidTruncationTelescopesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Copyright (c) 2026. Released under the Apache 2.0 license. Both verified unbounded truncation colimits become genuine mapping-cone quasi-isomorphisms in the protected Solid category. The colimit proofs are imported unchanged. Monicity reuses the actual AB5 sequence presentation; no unbounded completeness or generation premise is assumed. Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1.",
        H("Solid Truncation Telescopes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-solidtruncationtelescopes-soliduppertruncationtelescope"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/SolidTruncationTelescopes.solidUpperTruncationTelescope"),
                H("solid Upper Truncation Telescope"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual good upper telescope in Solid, with no boundedness premise."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-solidtruncationtelescopes-soliduppertruncationtelescopetoinput"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/SolidTruncationTelescopes.solidUpperTruncationTelescopeToInput"),
                H("solid Upper Truncation Telescope To Input"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Copyright (c) 2026. Released under the Apache 2.0 license. Both verified unbounded truncation colimits become genuine mapping-cone quasi-isomorphisms in the protected Solid category. The colimit proofs are imported unchanged. Monicity reuses the actual AB5 sequence presentation; no unbounded completeness or generation premise is assumed. Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-solidtruncationtelescopes-soliduppertruncationtelescopetoinput-quasiiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/SolidTruncationTelescopes.solidUpperTruncationTelescopeToInput_quasiIso"),
                H("solid Upper Truncation Telescope To Input quasi Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Copyright (c) 2026. Released under the Apache 2.0 license. Both verified unbounded truncation colimits become genuine mapping-cone quasi-isomorphisms in the protected Solid category. The colimit proofs are imported unchanged. Monicity reuses the actual AB5 sequence presentation; no unbounded completeness or generation premise is assumed. Research: Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1."))),
                DescribeRole.Theorem))));
}
