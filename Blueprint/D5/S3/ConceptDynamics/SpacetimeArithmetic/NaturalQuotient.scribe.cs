using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeArithmetic;

internal sealed class NaturalQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/SpacetimeArithmetic/NaturalQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Retain the nonnegative balanced history domain.",
        H("Retain the nonnegative balanced history domain"),
        Blocks(
            Paragraph(Text("Formula limitation: these dependent history and quotient declarations are "
                + "presented through resolving Lean declaration handles. WithoutFormula supplies no "
                + "independent formula transcription; the Lean declarations specify the exact statements.")),
            Describe.Lean(
                DescribeId.Create("nonnegative-history"),
                DeclarationHandle.Create(Prefix + "NonnegativeHistory"),
                H("Retain the nonnegative balanced history domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "NonnegativeHistory d is the subtype of actual BalancedRich d satisfying zero at most "
                        + "balancedQ. Histories, archive fields, and the nonnegative guard remain present before "
                        + "quotienting."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("numerical-iff-signed"),
                DeclarationHandle.Create(Prefix + "numerical_iff_signed"),
                H("Natural readout has exactly the signed equality kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On this nonnegative domain, casting naturalQ back to Int returns balancedQ. Thus the "
                        + "quotient kernel of naturalQ is precisely equality of signed readouts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("readout-semiring-equiv"),
                DeclarationHandle.Create(Prefix + "readoutSemiringEquiv"),
                H("The actual nonnegative quotient is the natural semiring"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The section uses representative d n for each natural n. Its right-inverse law gives the "
                        + "Mathlib quotient equivalence; semiring structure is transferred only onto that quotient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("zero-class"),
                DeclarationHandle.Create(Prefix + "zero_class"),
                H("Zero is the fixed natural zero class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Natural quotient zero is the class of naturalSection d 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-class"),
                DeclarationHandle.Create(Prefix + "one_class"),
                H("One is the fixed natural one class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Natural quotient one is the class of naturalSection d 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("add-class"),
                DeclarationHandle.Create(Prefix + "add_class"),
                H("Native parallel composition induces natural addition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "parallelNonnegative retains parallelBalanced together with its proved nonnegative "
                        + "readout. Its quotient class is the sum of the input classes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mul-class"),
                DeclarationHandle.Create(Prefix + "mul_class"),
                H("Native product induces natural multiplication"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "productNonnegative retains productBalanced together with its proved nonnegative readout. "
                        + "Its quotient class is the product of the input classes."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complement-nonnegative-iff"),
                DeclarationHandle.Create(Prefix + "complement_nonnegative_iff"),
                H("Complement stays nonnegative exactly at zero readout"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonnegative balanced history, native complement is still nonnegative if and "
                        + "only if its original readout is zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("complement-not-closed"),
                DeclarationHandle.Create(Prefix + "complement_not_closed"),
                H("Native complement is not closed on the nonnegative domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every spatial dimension, applying the preceding criterion to naturalSection d 1 "
                        + "refutes universal complement closure."))),
                DescribeRole.Theorem))));
}
