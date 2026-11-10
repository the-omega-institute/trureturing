using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ReadExecution;

internal sealed class OriginalJointRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite stochastic joint operations and their common fresh table realization.",
        H("Original joint stochastic execution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-joint-finite-execution-law"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ReadExecution/OriginalJointRealization.finite_execution_law"),
                H("The entire finite joint execution law"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix a finite complete configuration carrier C with measurable singletons, an emission tag, and two configurations carrying its two Boolean decisions. An original stochastic specification gives a joint initialization distribution and, for every complete configuration and acquired bit, a joint distribution of the intermediate configuration and ensuing action. A read action carries a none-tagged complete configuration; an emitted action carries a configuration with its own decision tag. These original joint distributions are specified without any innovation tape, and can correlate the update and action choice.")),
                    Paragraph(Text("One fresh innovation is a finite table with one joint outcome for every configuration and bit. Its distribution is the product of all original operation rows. The machine evaluates only the entry indexed by its actual complete configuration and newly read bit. Initialization samples the original joint initialization law. The table and initialization outcome are source independent. Neither table, source name, clock, acquired receipt nor unused random choices are retained in C.")),
                    Paragraph(Text("For every fixed source bit sequence and every natural allowance n, the original joint execution distribution is defined recursively by the original initialization and operation rows. Its vector records n+1 successive joint outcomes. After internal emission its previous outcome is held, with no read or operation. The table interpreter on an independent seed and n independent fresh tables has exactly this entire vector distribution. The statement retains both intermediate configurations and their correlated ensuing actions, and includes initial emission, arbitrary terminal configurations, null paths and allowance zero. It is an equality of measures on the complete finite trace space, not only of one-operation marginals.")),
                    Paragraph(Text("The induction separates the last fresh table from the preceding seed and tables. It transports the complete preceding trace distribution and integrates the selected original joint row. The finite table is an analytical representation of fresh randomness, not an accessible persistent random tape. The same original stochastic specification serves both source labels. Relating this finite representation to an infinite source product, original stopped receipts and renewal epoch laws requires the corresponding realization statements. No entropy, occupation or full E4 conclusion is asserted by the finite execution identity."))),
                DescribeRole.Theorem))));
}
