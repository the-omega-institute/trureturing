using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class FractionFieldDerivationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integer-linear derivation on an integral domain extends to every realization of its fraction field.",
        H("Derivations on Fraction Fields"),
        Blocks(
            Describe.Remark(
                DescribeId.Create("fraction-field-derivation-extension"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend"),
                H("The extended derivation"),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let R be an integral domain, F a fraction field of R, and D an integer-linear derivation from R to R. "
                    + "Map r to the dual number whose two coordinates are the images of r and D(r) in F. "
                    + "Every nonzero denominator maps to a unit because its first coordinate is nonzero. "
                    + "The universal property of localization extends this ring homomorphism to F. "
                    + "Its first coordinate is the identity on F, so its second coordinate is an integer-linear derivation. "
                    + "This construction is repository-derived from Mathlib's localization and trivial square-zero extension APIs.")))),
            Describe.Lean(
                DescribeId.Create("fraction-field-derivation-agreement"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_algebraMap"),
                H("Agreement on the original domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every r in R, the value of the extended derivation at the image of r in F equals the image of D(r). "
                    + "Consequently, a differential equation proved in the original domain remains valid after embedding into its fraction field."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fraction-field-derivation-uniqueness"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_unique"),
                H("Uniqueness of the extension"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any integer-linear derivation on F that agrees with D on the image of R equals the constructed extension. "
                    + "Indeed, every x in F satisfies xb=a for images of some a,b in R with b nonzero. "
                    + "Differentiating this identity determines b times the derivative of x, and cancellation of b determines that derivative uniquely."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fraction-field-derivation-commutation"),
                DeclarationHandle.Create("D5/S1/Recurrence/Algebraic/FractionFieldDerivation.extend_commutes"),
                H("Compatibility with further field extensions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let L be a field over F, with compatible embeddings of R, and let d be an integer-linear derivation on L. "
                    + "If d agrees with D on the embedded original domain R, then d commutes with the extended derivation on every element of F. "
                    + "The same differentiated identity xb=a proves the assertion after embedding into L and cancelling the image of the nonzero denominator b."))),
                DescribeRole.Theorem))));
}
