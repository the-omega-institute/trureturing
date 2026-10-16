using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class LocalizedCocycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LocalizedCocycle",
        H("Congruence after clearing a denominator"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("localizedcocycle-1"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/LocalizedCocycle.integerValues_mod_three"),
                H("Congruence after clearing a denominator"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let P be a rational multivariate polynomial, Q an integer polynomial, and D a nonzero integer with Q mapped to the rationals equal to D P. At both signed integer tuples x and y, the evaluations of P must be integers a and b. If every coordinate agrees modulo three to the power e plus one, where e bounds the three-adic valuation of D, then a and b agree modulo three. No positivity, finite-variable, or localization hypothesis is needed for this theorem.")),
                    Paragraph(Text("Integer polynomial evaluation respects reduction, so three to the power e plus one divides D times the difference b minus a. If that difference is zero the result is immediate; otherwise additivity of the three-adic valuation and the denominator bound imply that its valuation is at least one. This is the classical clearing-denominator congruence argument. No ring map from the rational coefficients to ZMod is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("localizedcocycle-2"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/LocalizedCocycle.dyadicReduction"),
                H("Reduction from the dyadic localization"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Two is a unit modulo every positive power of three. The universal property of localization therefore extends integer reduction to the localization of the integers away from two. Its restriction to every integer is the usual residue. This helper supplies the actual dyadic reduction used by the canonical rectangular cochain."))),
                DescribeRole.Theorem))));
}
