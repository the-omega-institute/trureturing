using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostRotatedFormDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Energy-rotated ordered ghost Hermitian form",
        H("Energy-rotated ordered ghost Hermitian form"),
        Blocks(
            Paragraph(Text("The carrier is the unrestricted native algebraic exterior bc Fock space over Complex. The actual energy half-turn uses integer zpow, including negative energies, and is not occupation parity, ghost number, charge reflection or antilinear PCT. Gplus rotates the right slot of the exact ordered reversed-word BPZ top coefficient; Hplus also conjugates the left coefficients. The actual zero-mode stress transpose and nonzero ordered kernel prove energy(chi(S))=energy(S). Actual finite common stress support intervals give all stress intertwining laws. Original b and c Hermitian transposes have respectively plus and minus occupation-parity signs; the stress transpose has no sign. Physical relative C0 forms and positivity remain separate. These are classical algebraic Fock and BPZ identities, with no physical or literature novelty claimed.")),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-energy-chi"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.energy_chi"),
                H("energy chi"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-rotation-transpose"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.rotation_transpose"),
                H("rotation transpose"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-rotation-conjugation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.rotation_conjugation"),
                H("rotation conjugation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-rotation-normalpair"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.rotation_normalPair"),
                H("rotation normalPair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-rotation-stress"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.rotation_stress"),
                H("rotation stress"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-gplus-c"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.Gplus_c"),
                H("Gplus c"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-gplus-stress"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.Gplus_stress"),
                H("Gplus stress"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-hplus-hermitian"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.Hplus_hermitian"),
                H("Hplus hermitian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-hplus-c"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.Hplus_c"),
                H("Hplus c"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-hplus-stress"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.Hplus_stress"),
                H("Hplus stress"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-pi-stress"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.Pi_stress"),
                H("Pi stress"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The compiled declaration supplies the exact native telescope, carriers and conditions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-rotation-support"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.rotation_support"),
                H("Actual rotation support"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The nonzero integer energy phase preserves the complete finite coefficient support exactly, including negative energies."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-hplus-degree-selection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.Hplus_degree_selection"),
                H("Rotated ghost degree selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual conjugated-left and energy-rotated-right BPZ pairing vanishes unless the two ghost degrees sum to three."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-hplus-c0-degree-selection"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.Hplus_c0_degree_selection"),
                H("Rotated inserted ghost degree selection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual original c(0) raises degree by one, so the rotated inserted pairing vanishes unless the original ghost degrees sum to two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bcghostrotatedform-hplus-j-k"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/BcGhostRotatedForm.Hplus_j_k"),
                H("Exact rotated insertion phase"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact original j,k kernel is minus one. This finite sign computation is consumed by native inserted normalization and is not a new abstract positivity theorem."))),
                DescribeRole.Theorem))));
}
