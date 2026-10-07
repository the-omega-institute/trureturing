using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra.Solid;

internal sealed class DiscreteIntDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "# Algebra for the proof that `ℤ` is solid This file contains the finite-support sequence calculation used in the proof that the light condensed abelian group of integers is solid. The finite-difference operator `a ↦ (fun n => a n - a (n + 1))` is an automorphism of finitely supported integer sequences, with inverse given by finite tail sums.",
        H("Discrete Int"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("solid-discreteint-oneminusshift-component-isiso"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DiscreteInt.oneMinusShift_component_isIso"),
                H("one Minus Shift component is Iso"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. # Algebra for the proof that `ℤ` is solid This file contains the finite-support sequence calculation used in the proof that the light condensed abelian group of integers is solid. The finite-difference operator `a ↦ (fun n => a n - a (n + 1))` is an automorphism of finitely supported integer sequences, with inverse given by finite tail sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("solid-discreteint-issolid-int"),
                DeclarationHandle.Create("D5/S3/HomologicalAlgebra/Solid/DiscreteInt.isSolid_int"),
                H("is Solid int"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration is supplied by the compiled Lean source. # Algebra for the proof that `ℤ` is solid This file contains the finite-support sequence calculation used in the proof that the light condensed abelian group of integers is solid. The finite-difference operator `a ↦ (fun n => a n - a (n + 1))` is an automorphism of finitely supported integer sequences, with inverse given by finite tail sums."))),
                DescribeRole.Theorem))));
}
