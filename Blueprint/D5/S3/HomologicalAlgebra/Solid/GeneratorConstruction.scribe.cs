using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class GeneratorConstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual ordinary P reflection is imported; new concrete finite-approximation retract, degree-zero DSolid realization of every reflected free profinite generator, the actual ordinary generator solidification(P), the exact local reflector, protected derived coproduct preservation, and the concrete unbounded lower-truncation telescope. Only new owned construction bodies are assembled to share one import pass. Passed dependencies are imported unchanged. New proofs: Apache-2.0. Research: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Theorem 3.3.1 and Lemma 3.3.2. No arbitrary unbounded realization or original HasLeftDerivedFunctor/derived adjunction is assumed.",
        H("Generator Construction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-generatorconstruction-localfreestalkordinaryrealizationiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/GeneratorConstruction.localFreeStalkOrdinaryRealizationIso"),
                H("local Free Stalk Ordinary Realization Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The generator realization uses the exact original ordinary reflector."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("solid-generatorconstruction-solidp-detects-iszero"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/GeneratorConstruction.solidP_detects_isZero"),
                H("solid P detects is Zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual protected object solidification(P), rather than an assumed generator, detects every zero solid object."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-generatorconstruction-lowertruncationtelescopetoinput-quasiiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/GeneratorConstruction.lowerTruncationTelescopeToInput_quasiIso"),
                H("lower Truncation Telescope To Input quasi Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A proved quasi-isomorphism for every unbounded input. It provides the actual lower-truncation telescope used in the realization argument."))),
                DescribeRole.Theorem))));
}
