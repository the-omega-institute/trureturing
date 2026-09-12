using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeArithmetic;

internal sealed class IntegerQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/SpacetimeArithmetic/IntegerQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Balanced histories modulo signed readout form the integer ring.",
        H("Balanced histories modulo signed readout form the integer ring"),
        Blocks(
            Paragraph(Text("Formula limitation: these dependent history and quotient declarations are "
                + "presented through resolving Lean declaration handles. WithoutFormula supplies no "
                + "independent formula transcription; the Lean declarations specify the exact statements.")),
            Describe.Lean(
                DescribeId.Create("readout-ring-equiv"),
                DeclarationHandle.Create(Prefix + "readoutRingEquiv"),
                H("Balanced histories modulo signed readout form the integer ring"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The carrier is Quotient of the kernel of balancedQ on the actual BalancedRich d. The "
                        + "fixed balancedSection is a right inverse. Mathlib transfers the integer ring structure "
                        + "onto this quotient and provides the readout ring equivalence. No ring is assigned to "
                        + "either raw carrier."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("class-eq-iff"),
                DeclarationHandle.Create(Prefix + "class_eq_iff"),
                H("Numerical equivalence is exactly equality of classes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The quotient identifies precisely histories with equal signed readout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-class"),
                DeclarationHandle.Create(Prefix + "zero_class"),
                H("Zero is the fixed empty representative class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Quotient zero is the class of balancedSection d 0, whose underlying history is "
                        + "representative d 0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("one-class"),
                DeclarationHandle.Create(Prefix + "one_class"),
                H("One is the fixed value-one representative class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Quotient one is the class of balancedSection d 1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("add-class"),
                DeclarationHandle.Create(Prefix + "add_class"),
                H("Addition is induced by native parallel composition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all balanced histories the sum of their classes equals the class of the B2 "
                        + "parallelBalanced operation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mul-class"),
                DeclarationHandle.Create(Prefix + "mul_class"),
                H("Multiplication is induced by the archive-preserving product"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all balanced histories the product of their classes equals the class of the B2 "
                        + "productBalanced operation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("neg-class"),
                DeclarationHandle.Create(Prefix + "neg_class"),
                H("Negation is induced by event complement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The negative of each class is the class of its B1 native complementBalanced history."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("readout-ring-equiv-unique"),
                DeclarationHandle.Create(Prefix + "readoutRingEquiv_unique"),
                H("The specified action uniquely determines the ring equivalence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any ring equivalence to Int acting as balancedQ on every representative class equals "
                        + "readoutRingEquiv. The preceding readout_unique theorem proves this even among functions."))),
                DescribeRole.Theorem))));
}
