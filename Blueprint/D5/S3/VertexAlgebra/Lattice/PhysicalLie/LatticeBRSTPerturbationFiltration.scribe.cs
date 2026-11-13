using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.PhysicalLie;

internal sealed class LatticeBRSTPerturbationFiltrationDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("latticebrstperturbationfiltration-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/PhysicalLie/LatticeBRSTPerturbationFiltration." + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed energy and signed filtration for the original lattice BRST charge",
        H("Fixed energy and signed filtration for the original lattice BRST charge"), Blocks(
            Paragraph(Text("The carrier is the actual State D, the all-charge lattice matter carrier tensored with the original countable bc occupation Fock space. D and its rank, null frame F, transverse dimension t and basis B retain their original quantifiers. H has both inverse-Gram hypotheses wherever the source requires them. Charge beta is integral; level and filtration lower are arbitrary integers. Q is the original LatticeBRST.totalCharge D H, and all basis statements use the original actualBasis F B.")),
            Paragraph(Text("This publication characterizes the literal fixed charge and energy sector. The signed bounds and operator restrictions are preserved with the complete future finite-transfer source; their compilation is not claimed here. The original signed degree and both exceptional ghost occupations remain unchanged in that source. This does not assert a physical no-ghost theorem.")),
            Node("groundEnergy", "Charge ground energy", "For every lattice D and integral charge beta, groundEnergy beta is bilinear D beta beta, cast to C, divided by 2.", DescribeRole.Definition),
            Node("totalL0", "Actual total zero mode", "For every D and matrix H of size Fin D.rank, totalL0 H is the original matter mode at 0 plus the original ghost Virasoro mode at 0, on the full State D.", DescribeRole.Definition),
            Node("oscillatorLevel", "Oscillator frequency level", "For every transverse dimension t and exponent vector m, oscillatorLevel m is Finsupp.weight frequencyWeight m.", DescribeRole.Definition),
            Node("indexLevel", "Integer level of every raw occupation", "For every StateIndex D t, indexLevel is oscillatorLevel plus BcGhostRelativeEnergy.relativeEnergy of the raw ghost occupation. No occupation is discarded.", DescribeRole.Definition),
            Node("totalL0_basis", "Energy of the actual basis", "For every D, null frame F, transverse basis B, H satisfying both H * gramComplex D = 1 and gramComplex D * H = 1, and every i, totalL0 H applied to actualBasis F B i equals (groundEnergy i.1.1 + (indexLevel i : C) - 1) times that same basis vector.", DescribeRole.Theorem),
            Node("totalL0_diagonal", "Diagonal form on the actual basis", "For the same arbitrary D, F, B and H with both inverse-Gram identities, totalL0 H is diagonal on actualBasis F B with eigenvalue groundEnergy i.1.1 + (indexLevel i : C) - 1.", DescribeRole.Theorem),
            Node("fixedSector", "Literal fixed charge and total energy", "For every D, H, integral charge beta and integer level, fixedSector H beta level is the submodule of the full State D defined by chargeProject beta v = v and totalL0 H v = (groundEnergy beta + (level : C) - 1) times v. There is no global energy cutoff.", DescribeRole.Definition),
            Node("mem_fixedSector_iff", "Exact coefficient characterization of the sector", "For arbitrary F and B and both inverse-Gram identities for H, v belongs to fixedSector H beta level if and only if every nonzero actualBasis coefficient has charge beta and indexLevel equal to level. All integer levels remain quantified.", DescribeRole.Theorem),
            Node("signedFiltration", "Original signed filtration", "For arbitrary beta and integers level and lower, signedFiltration F B beta level lower is the C-span of the actual basis vectors with charge beta, indexLevel equal to level and lower <= degree. It is a submodule of the original State D.", DescribeRole.Definition),
            Paragraph(Text("The original State D, total charge, both inverse-Gram hypotheses, arbitrary rank and all integer levels are retained. The coefficient characterization and its two consumed energy helpers are the three current public theorems. Their escape audits remain unfinished in issue 30101; the characterization has no certified escape-witness classification.")))));
}
