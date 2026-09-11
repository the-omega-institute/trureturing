using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.SpacetimeArithmetic;

internal sealed class RationalQuotientDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/SpacetimeArithmetic/RationalQuotient.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The quotient of actual rich fractions is the standard rational field via its reduced section.",
        H("The Rational Field Quotient"),
        Blocks(
            Paragraph(Text("Formula projection does not express the dependent archive carriers here. "
                + "The resolving Lean handles carry the typed statements; this narrative supplies no separate formula.")),
            Describe.Lean(
                DescribeId.Create("canonical-section"),
                DeclarationHandle.Create(Prefix + "rationalSection_rightInverse"),
                H("The reduced rational section is a right inverse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The numerator is balancedSection d r.num and the denominator is balancedSection d r.den, "
                        + "using Rat's reduced coordinates. Rat.num_div_den proves the right inverse; zero is "
                        + "literally the canonical zero-over-one pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-reduced"),
                DeclarationHandle.Create(Prefix + "rationalSection_reduced"),
                H("The canonical denominator is positive and the coordinates are coprime"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Rat.den_pos and Rat.reduced give the positive denominator and coprime absolute integer "
                        + "coordinates after the balanced section readout equations."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unique-coordinates"),
                DeclarationHandle.Create(Prefix + "reduced_coordinates_unique"),
                H("Reduced positive coordinates are unique"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Rat.div_int_inj proves that any coprime integer coordinates with a positive denominator "
                        + "and the same rational value equal Rat.num and Rat.den. This uniqueness does not identify "
                        + "arbitrary histories."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quotient-equivalence"),
                DeclarationHandle.Create(Prefix + "rational_quotient_equiv"),
                H("The actual kernel quotient is equivalent to Rat"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Setoid.quotientKerEquivOfRightInverse is applied directly to the full Fraction d carrier, "
                        + "its readout and the proved canonical section. The forward map sends each class to its "
                        + "readout."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-equivalence"),
                DeclarationHandle.Create(Prefix + "rational_field_equiv"),
                H("Field structure is transported along the equivalence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Equiv.field supplies the field instance on the kernel quotient, and Equiv.ringEquiv gives "
                        + "the ring equivalence to Rat. Class addition, multiplication and negation are proved to "
                        + "agree with the native rich formulas."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("quotient-inverse"),
                DeclarationHandle.Create(Prefix + "class_inv"),
                H("Quotient inverse agrees on the legal rich domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The class of the guarded native inverse equals the field inverse. The field convention at "
                        + "zero is part of the quotient field and does not extend the partial rich operation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quotient-division"),
                DeclarationHandle.Create(Prefix + "class_div"),
                H("Quotient division agrees on the legal rich domain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The class of the native cross-product division equals field division. The two "
                        + "quotient-domain theorems identify the rich guards with nonzero quotient classes."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/ConceptDynamics/SpacetimeArithmetic/RichRational"))
        ]));
}
