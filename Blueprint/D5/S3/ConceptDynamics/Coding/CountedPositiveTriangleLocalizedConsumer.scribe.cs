using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class CountedPositiveTriangleLocalizedConsumerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CountedPositiveTriangleLocalizedConsumer",
        H("The same signed integer gyration lift"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("existing-six-countedpositivetrianglelocalizedconsumer-centralizer-product"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.centralizer_product"),
                H("The triangle becomes a product law along a centralizing unit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a monoid, a fixed element A and a ZMod 3-valued function satisfying the stated triangle identity, commuting U with A splits the value on U times V into the two unit contributions. Only U is required to commute with A in this identity. It supplies the multiplicative law for the constructed centralizer character."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("existing-six-countedpositivetrianglelocalizedconsumer-integergyrationvalue-nat-mod-three"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue_nat_mod_three"),
                H("The natural-input signed lift has the original residue"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonnegative rectangular factors and a nonzero period divisible by three, reduction of the signed integer evaluator agrees with the reduced relative forward gyration. The comparison retains the original ranked periodic action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("localizedcocycle-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerValues_mod_three"),
                H("Congruence after clearing a denominator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let P be a rational multivariate polynomial, Q an integer polynomial, and D a nonzero integer with Q mapped to the rationals equal to D P. At both signed integer tuples x and y, the evaluations of P must be integers a and b. If every coordinate agrees modulo three to the power e plus one, where e bounds the three-adic valuation of D, then a and b agree modulo three. No positivity, finite-variable, or localization hypothesis is needed for this theorem.")),
                    Paragraph(Text("Integer polynomial evaluation respects reduction, so three to the power e plus one divides D times the difference b minus a. If that difference is zero the result is immediate; otherwise additivity of the three-adic valuation and the denominator bound imply that its valuation is at least one. This is the classical clearing-denominator congruence argument. No ring map from the rational coefficients to ZMod is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("localizedcocycle-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.dyadicReduction"),
                H("Reduction from the dyadic localization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Two is a unit modulo every positive power of three. The universal property of localization therefore extends integer reduction to the localization of the integers away from two. Its restriction to every integer is the usual residue. This helper supplies the actual dyadic reduction used by the canonical rectangular cochain."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedpositivetrianglelocalizedconsumer-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue"),
                H("The same signed integer gyration lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The integer value at a compatible rectangular pair is exactly the accepted signedGyrationLift applied to the two matrices through Sum.elim. Its binomial-coefficient formula is integer valued on arbitrary signed tuples. It agrees on natural tuples with the accepted order-type lift; no new invariant is substituted."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("countedpositivetrianglelocalizedconsumer-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.orderTypeGyrationLift_positive_triangle_mod_three"),
                H("Transport the actual triangle to the integer lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The accepted equality between actual relative forward gyration and the order-type lift, followed by integer-cast compatibility, transports the proved numbered-path triangle modulo three. The same n,m,p and nonzero period divisible by three remain in scope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("countedpositivetrianglelocalizedconsumer-3"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/CountedPositiveTriangleLocalizedConsumer.integerGyrationValue_nonnegative_triangle"),
                H("Include zero entries and empty intermediate dimensions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Entrywise toNat recovers a nonnegative integer matrix exactly. Matrix.map_mul transports all three products back to the natural counted triangle. The equality of the signed and natural binomial lifts then proves the integer triangle on nonnegative entries. Products may vanish when the intermediate dimension is zero, which is why this nonnegative statement is used instead of strict positivity of products."))),
                DescribeRole.Theorem))));
}
