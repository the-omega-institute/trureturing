using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class KhetanOneDirectionPeriodizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Algebraic periodizer bridge for finite-alphabet lattice configurations.",
        H("KhetanOneDirectionPeriodizer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exact-cover-product-differences"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.exact_cover_product_differences"),
                H("Exact-cover annihilator of the original configuration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive-shift operators use the negative-exponent tile mask. Exact coverage makes that mask act as the constant one configuration. A lattice difference supplies a nonzero annihilator, and the pinned product-difference supplier acts directly on the original integer configuration."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonzero-line-annihilator-periodic"),
                DeclarationHandle.Create("D5/S1/Dynamics/Symbolic/KhetanOneDirectionPeriodizer.nonzero_line_annihilator_periodic"),
                H("From a line annihilator to a global period"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every nonzero polynomial annihilator in a nonzero lattice direction yields a nonzero period of the original finite-range configuration. No periodic-line conclusion or nonzero constant coefficient is assumed. This is the terminal recurrence step, not the complete one-direction periodizer theorem."))),
                DescribeRole.Theorem))));
}
