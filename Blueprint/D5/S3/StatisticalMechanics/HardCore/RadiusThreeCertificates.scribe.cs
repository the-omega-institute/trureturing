using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class RadiusThreeCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric hard-core branching, exact certificates and their precise scope.",
        H("RadiusThreeCertificates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthreemask"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeMask"),
                H("Actual blocked vertices"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The explicit integer code decodes to a finite subset of the Manhattan radius-three disk."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthreestep"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeStep"),
                H("Geometrically computed transitions"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An unblocked move computes memoryStep and looks up its exact encoded successor. The closure theorem proves that this lookup cannot omit a legal move."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthreelower"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeLower"),
                H("All-order sub-potential"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonnegative integer weights certify a lower rate for every allowed ordering. Zero weights are allowed on dead states."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthreeupper"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeUpper"),
                H("Selected-policy super-potential"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Strictly positive integer weights certify the chosen adaptive controller. Every state is checked."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthreefixedlower"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeFixedLower"),
                H("Fixed-SRL sub-potential"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A separate integer witness provides a lower growth rate for the same geometric memory model under fixed SRL ordering."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthreechoice"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThreeChoice"),
                H("Concrete adaptive ordering"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each represented blocked set selects one of the six permutations. This is an explicit stationary controller."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthree-geometry"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_geometry"),
                H("Complete geometric closure"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The statement checks cardinality, distinct codes, the initial parent mask, parent and origin conditions, and every state-order-direction successor. This is closure of the finite geometric presentation, not sampled path coverage."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthree-potentials"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_potentials"),
                H("Exact arithmetic certificates"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All-order lower rows use 5041 and 2000; selected-policy upper rows use 12603 and 5000; fixed-SRL lower rows use 25209 and 10000. Initial weights and the cap are one billion. The proof script requests kernel reduction of the actual data."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthree-adaptive-upper"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_adaptive_upper"),
                H("An all-depth adaptive upper bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the generic induction to the concrete selected controller. The conclusion retains the explicit state-dependent prefactor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthree-all-controllers-lower"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_all_controllers_lower"),
                H("A floor for every controller"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("From the initial state, every policy has at least the displayed exponential descendant count. The quantifier includes arbitrary dependence on the entire direction history. This lower bound belongs to the truncated memory model and cannot be transferred as a grid lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthree-fixed-order-lower"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_fixed_order_lower"),
                H("A larger fixed-order lower bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed-SRL relaxed tree has lower rate 2.5209, exceeding the selected adaptive upper rate 2.5206. The all-depth integer inequalities imply the asymptotic comparison."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hard-core-radiusthreecertificates-radiusthree-finite-domain-upper"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/RadiusThreeCertificates.radiusThree_finite_domain_upper"),
                H("An actual finite-grid-domain consumer"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite integer-grid vertex domain with its parent absent, the actual ordered deletion count satisfies the explicit upper bound. Geometry discharges the table-coverage premises. Identification with the partition-function recursion and the complex zero-free transfer remain outside this theorem."))),
                DescribeRole.Theorem),
            Paragraph(Text("The sources were logically reviewed and the concrete certificates independently replayed using exact integers. Lean elaboration, axiom-print execution and Scribe emission were not performed in the authoring runtime. These candidate sources do not assert an improved global zero-free threshold.")))));
}
