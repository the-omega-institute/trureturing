using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class TelescopeEquivalenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The saved telescope and the saved ordinary cellular colimit are quasi-isomorphic for every arbitrary unbounded input. New proofs, released under the Apache 2.0 license.",
        H("Telescope Equivalence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-telescopeequivalence-solidcellulartelescopetocolimit-quasiiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/TelescopeEquivalence.solidCellularTelescopeToColimit_quasiIso"),
                H("solid Cellular Telescope To Colimit quasi Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual mapping telescope is quasi-isomorphic to the actual cellular colimit, for every input and every integer homology degree."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-telescopeequivalence-solidcellulartelescope-homology-solid"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/TelescopeEquivalence.solidCellularTelescope_homology_solid"),
                H("solid Cellular Telescope homology solid"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The telescope itself is now genuinely derived-local."))),
                DescribeRole.Theorem))));
}
