using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves;

internal sealed class Q9PairedGeometricObstructionDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9PairedGeometricObstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The paired syndrome forces signed squared energy at least 48.",
        H("The paired syndrome forces signed squared energy at least 48"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("paired-energy-ge-48-native"),
                DeclarationHandle.Create(Module + ".paired_energy_ge_48_native"),
                H("The paired syndrome forces signed squared energy at least 48"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Use the fixed little-endian Q8 chart. The word vanishes on even vertices, its odd coefficients occur exactly on the paired syndrome, and its signed adjacency is divisible by four at every vertex.")),
                    Paragraph(Text("Put unit signs on the sixteen syndrome sites. The two-neighbor structure and Huang's squared operator identity give exactly 32 nonzero rows. Each requires a correction. An exterior correction reaches at most four rows and costs at least four units of energy. An interior correction reaches at most eight rows and costs at least eight. Counting the rows gives the bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("no-paired-fold-at-order-72"),
                DeclarationHandle.Create(Module + ".no_paired_fold_at_order_72"),
                H("The paired syndrome excludes the order-72 signed fold"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume both signed fold equations, disjoint even dimer and even singleton words, dimer squared norm twelve, and combined singleton squared norm forty-eight. The fold implies even singleton squared norm sixteen.")),
                    Paragraph(Text("If the signed residual is supported on the odd half and its odd coefficients occur at exactly the fixed paired syndrome, the energy bound instead forces even singleton squared norm at least twenty-four. This is a conditional obstruction for the study of Hong–Wu–Xia, Section 7, Problem 2. https://arxiv.org/html/2610.09483v1#Thmproblem2"))),
                DescribeRole.Theorem)),
        []));
}
