using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class FiniteApproximationFamilyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The genuine continuous family (n,s) -> r_n(s), with infinity row s -> s, for the compatible finite approximations of an arbitrary light profinite S. Continuity is proved coordinatewise in the actual finite presentation: each projected family is eventually the projection itself as a continuous map, uniformly for all s. Empty, finite and infinite S are all allowed. New proofs, Apache-2.0. Research construction: Juan Esteban Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.",
        H("Finite Approximation Family"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationfamily-finiteapproximationfamily-finiteslice"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationFamily.finiteApproximationFamily_finiteSlice"),
                H("finite Approximation Family finite Slice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The genuine continuous family (n,s) -> r_n(s), with infinity row s -> s, for the compatible finite approximations of an arbitrary light profinite S. Continuity is proved coordinatewise in the actual finite presentation: each projected family is eventually the projection itself as a continuous map, uniformly for all s. Empty, finite and infinite S are all allowed. New proofs, Apache-2.0. Research construction: Juan Esteban Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-finiteapproximationfamily-finiteapproximationfamily-inftyslice"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/FiniteApproximationFamily.finiteApproximationFamily_inftySlice"),
                H("finite Approximation Family infty Slice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The genuine continuous family (n,s) -> r_n(s), with infinity row s -> s, for the compatible finite approximations of an arbitrary light profinite S. Continuity is proved coordinatewise in the actual finite presentation: each projected family is eventually the projection itself as a continuous map, uniformly for all s. Empty, finite and infinite S are all allowed. New proofs, Apache-2.0. Research construction: Juan Esteban Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2."))),
                DescribeRole.Theorem))));
}
