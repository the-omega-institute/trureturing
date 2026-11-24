using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Jacobi;

internal sealed class NeumannHeatGramianInverseDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Jacobi/NeumannHeatGramianInverse.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse coefficients of the centered heat Gramian identify a positive ordered path of known total length. Exchanging the final two unequal edges shows the least degree needed in a full jet.",
        H("The sharp finite Gramian jet of a positive Neumann path"),
        Blocks(
            Describe.Lean(DescribeId.Create("cubic-coefficient"), DeclarationHandle.Create(Prefix + "cubic_coefficient"),
                H("The cubic coefficient of the centered physical Gramian"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a positive path with at least one edge, write a for the length of its first edge. The Gramian coefficients of degrees zero, one, and two vanish. The coefficient of degree three is 4/(3a^6) for every additive constant in the heat response.")),
                    Paragraph(Text("In the formal variance the constant and quadratic heat coefficients cancel from the cubic term. The remaining term is the square of the linear heat coefficient divided by twelve. The lumped endpoint mass is a/2, so the first physical moment is 4/a^3."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("readout-degree"), DeclarationHandle.Create(Prefix + "readoutDegree"),
                H("Degree of the readout at each edge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For edges indexed from zero at the measured endpoint, the readout degree is three at index zero and 2k+2 at index k greater than zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sparse-injective"), DeclarationHandle.Create(Prefix + "sparse_injective"),
                H("Sparse finite injectivity at equal total length"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let two positive paths each have n edges and equal total lengths. If the Gramian coefficients at the readout degrees for the first n-1 edges agree, their ordered lengths coincide. The two heat responses may have independent constant offsets. The readout set is empty for n at most one.")),
                    Paragraph(Text("A difference at the first edge changes the cubic coefficient because a maps strictly decreasingly to 4/(3a^6). A first difference at a positive edge index changes the coefficient at that index's readout degree by the Jacobi prefix theorem. The equal sum determines the final edge once the preceding edges agree."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("jet-cutoff"), DeclarationHandle.Create(Prefix + "jetCutoff"),
                H("Least degree of the full jet"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cutoff is zero for at most one edge. For two or more edges it is the readout degree of the penultimate edge, which is three for two edges and 2n-2 for n at least three."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-jet-injective-iff"), DeclarationHandle.Create(Prefix + "finite_jet_injective_iff"),
                H("The full jet identifies the path exactly at and above the cutoff"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix the number of edges and a positive total length. Agreement through degree d determines the ordered path for any independent constant heat offsets if and only if d is at least the cutoff.")),
                    Paragraph(Text("The jet through the cutoff contains every sparse readout. For sharpness with n at least two, give the first n-1 edges length L/(n+1) and the last edge twice that length. Swapping the last two edges preserves positivity and the total L. The first differing edge is the penultimate one, and the Gramian coefficients agree at every degree below its readout degree."))), DescribeRole.Theorem))));
}
