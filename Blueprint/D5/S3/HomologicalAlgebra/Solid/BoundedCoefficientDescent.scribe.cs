using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class BoundedCoefficientDescentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Descent of the bounded coefficient maps to the actual condensed object B_Z. This constructs D : P tensor B_Z -> P as an honest condensed morphism. New proofs, Apache-2.0; the construction is the coefficient map in Rodríguez Camargo's Notes on Solid Geometry, Lemma 3.3.3.",
        H("Bounded Coefficient Descent"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-boundedcoefficientdescent-boundedmeasurecoefficient-on-section"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BoundedCoefficientDescent.boundedMeasureCoefficient_on_section"),
                H("bounded Measure Coefficient on section"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("D agrees with the concrete coefficient selector map on every actual bounded test section. This is the required descent comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-boundedcoefficientdescent-boundedmeasurecoefficient-on-family"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/BoundedCoefficientDescent.boundedMeasureCoefficient_on_family"),
                H("bounded Measure Coefficient on family"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. Descent of the bounded coefficient maps to the actual condensed object B_Z. This constructs D : P tensor B_Z -> P as an honest condensed morphism. New proofs, Apache-2.0; the construction is the coefficient map in Rodríguez Camargo's Notes on Solid Geometry, Lemma 3.3.3."))),
                DescribeRole.Theorem))));
}
