using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fermionic;

internal sealed class BcGhostOccupationRadiusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite radii on the original ghost Fock carrier",
        H("Finite radii on the original ghost Fock carrier"), Blocks(
            Paragraph(Text("The radius uses even sites 2j with j<A-1 and odd sites 2j+1 with j<A+2. Every finite-excitation vector admits such a radius. The bounds are purely algebraic, and use the original occupation creation and annihilation operators.")),
            Describe.Lean(
                DescribeId.Create("bcghostoccupationradius-sites"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.sites"),
                H("The actual b/c creator-site prefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For A at least two, the even creator labels range from minus A to minus two and the odd creator labels range from minus A to one. This parity-sensitive prefix is the cutoff used by the tensor coupling."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bcghostoccupationradius-radius"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.Radius"),
                H("Finite support inside the actual prefix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Radius A w means that every occupation in the finitely supported state w is a subset of sites A."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bcghostoccupationradius-exists-radius"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.exists_radius"),
                H("Every original ghost state has a radius"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every w in the original complex countable occupation Fock carrier, there is a natural A at least two with Radius A w. The largest site in the union of the finite support supplies a bound."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostoccupationradius-high-modes"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.high_modes"),
                H("The actual positive ghost tails vanish"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every A at least two, state w in Radius A and integer t>A, both b_t w and c_t w vanish. The proof uses their exact odd and even annihilation indices, not an imposed truncation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostoccupationradius-mode-radius"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.mode_radius"),
                H("Single-mode occupation growth"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original state in radius A at least two and integer t, both b_t w and c_t w lie in radius max(A,abs(t),2). Annihilation erases a site and creation inserts the site specified by the original mode."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostoccupationradius-virasoro-radius"),
                DeclarationHandle.Create("D5/S3/Quantum/Fermionic/BcGhostOccupationRadius.virasoro_radius"),
                H("The original ghost Virasoro radius bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every integer r, the original locally finite L_r maps Radius A into Radius A+max(0,-r). The finite normal-order sum is captured on q in [r-A,A]. In the right normal-order branch the b annihilator preserves Radius A before the c high-mode cutoff is used."))), DescribeRole.Theorem))));
}
