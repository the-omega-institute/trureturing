using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class BoundedObjectDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual bounded-integer-sequence condensed abelian group. Its presheaf consists of integer-measure sections with a single bound on all coordinates. Sheafification is left exact, so its inclusion in integer measures is a genuine monomorphism. No derived realization or projective-resolution assumption is used. New proofs, Apache-2.0. Research construction: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Lemmas 3.3.3--3.3.4, and root's immutable checked realization response. The retained supplier and official Mathlib attributions are unchanged.",
        H("Bounded Object"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-boundedobject-boundedintegersections-restrict"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BoundedObject.boundedIntegerSections_restrict"),
                H("bounded Integer Sections restrict"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual bounded-integer-sequence condensed abelian group. Its presheaf consists of integer-measure sections with a single bound on all coordinates. Sheafification is left exact, so its inclusion in integer measures is a genuine monomorphism. No derived realization or projective-resolution assumption is used. New proofs, Apache-2.0. Research construction: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Lemmas 3.3.3--3.3.4, and root's immutable checked realization response. The retained supplier and official Mathlib attributions are unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-boundedobject-freesectionequiv-coordinate"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BoundedObject.freeSectionEquiv_coordinate"),
                H("free Section Equiv coordinate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. The actual bounded-integer-sequence condensed abelian group. Its presheaf consists of integer-measure sections with a single bound on all coordinates. Sheafification is left exact, so its inclusion in integer measures is a genuine monomorphism. No derived realization or projective-resolution assumption is used. New proofs, Apache-2.0. Research construction: Juan Esteban Rodríguez Camargo, Notes on Solid Geometry, Lemmas 3.3.3--3.3.4, and root's immutable checked realization response. The retained supplier and official Mathlib attributions are unchanged."))),
                DescribeRole.Theorem))));
}
