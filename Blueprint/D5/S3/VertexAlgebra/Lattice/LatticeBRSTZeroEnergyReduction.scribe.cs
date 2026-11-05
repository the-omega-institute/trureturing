using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeBRSTZeroEnergyReductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full BRST quotient reduction and the physical Delta", H("Full BRST quotient reduction and the physical Delta"), Blocks(
            Paragraph(Text("The carrier is the original all-charge lattice/oscillator tensor the complete ghost Fock space. Its basis is indexed by the full lattice positive-energy label together with a finite ghost-occupation set, so State D retains charge, every oscillator, and every ghost occupation. totalL0 D H is the actual matter-mode-zero plus ghost Virasoro operator. The total energy diagonalizes on that basis; P0 is the literal spectral projector for total energy zero, EInv is the coefficientwise inverse away from zero, and h is the original B0 composed with EInv. The only critical hypotheses are rank D = 26 and the two inverse-Gram equations H * gramComplex D = 1 and gramComplex D * H = 1 whenever a quotient or homotopy theorem below is used.")),
            Paragraph(Text("The Ward identity Q B0 + B0 Q = totalL0, together with the rank-26 square-zero identity for Q = totalCharge D H, gives the nontrivial homotopy identity Q h + h Q = 1 - P0. Hence every Q-cycle x satisfies x - P0 x = Q (h x), so projection changes no class in the existing full kernel modulo image quotient. The negative boundary primitive is retained as an internal proof step: for every preimage y, Q (-(B0 (P0 y))) = B0 (P0 (Q y)); it follows from the Ward identity, Q/P0 commutation, and totalL0 P0 = 0 and supplies the actual quotient boundary transfer. This is a zero-energy representative choice inside the full quotient, not a relative, b0, ground-state, finite-cutoff, positivity, or finite-dimensional replacement.")),
            Paragraph(Text("The source inherits Bakalov--Kac's lattice construction, Scott Carnahan's vertexAlg field/residue calculus (revision 4453e34ec390e82a0c789c731ada8f9a6e86bdea), Kalle Kytola's Sugawara suppliers, the original ghost-state construction, and Mathlib quotient and linear-algebra machinery. The current native source is an immutable supplier snapshot; no literature novelty, independent verification, official acceptance, or complete string-theory or AdS/CFT result is asserted.")),
            Describe.Lean(DescribeId.Create("original-brst-reduction-p0"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction.P0"),
                H("The literal total-energy-zero projector on the full state carrier"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Definition at native source lines 74--75. P0 is energyWeight with coefficient 1 exactly at totalEnergy D label = 0 and 0 otherwise, acting on the complete charge/oscillator/ghost basis. It has no rank or Gram argument itself; its use in Q-cycle and quotient statements is governed by the explicit hypotheses on those theorems."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-brst-reduction-homotopy-identity"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction.homotopy_identity"),
                H("The full-state contracting homotopy identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Theorem at native source lines 309--325. For D, H, h26 : D.rank = 26, hHG : H * gramComplex D = 1, and hGH : gramComplex D * H = 1, the original h = B0 composed with EInv satisfies totalCharge D H * h + h * totalCharge D H = 1 - P0 D. The proof uses the actual Ward identity and EInv's spectral inverse, not an assumed homotopy law."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-brst-reduction-cycle-reduction"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction.cycle_reduction"),
                H("Every full BRST cycle is homologous to its actual zero-energy projection"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Theorem at native source lines 337--344. Under the same rank-26 and two inverse-Gram hypotheses, if totalCharge D H x = 0 then x - P0 D x = totalCharge D H (h D x). This is the explicit boundary witness that transfers arbitrary full-state cycles to P0 representatives while preserving the original quotient."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-brst-reduction-delta"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction.Delta"),
                H("The P0-reduced physical antighost on the existing full cohomology quotient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Definition at native source lines 455--461. Delta is the quotient endomorphism induced by cycleDelta = B0 composed with P0 on the actual cycles, after the source proves that this map preserves the actual boundaries using the negative primitive. Its domain is the existing Cohomology D H h26 hHG hGH, with all original charge, oscillator, and ghost states retained."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("original-brst-reduction-delta-classof"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction.Delta_classOf"),
                H("Delta on every actual cycle class"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Theorem at native source lines 465--483. For every cycles D H representative x under rank 26 and both inverse-Gram laws, Delta (classOf x) is the class of the genuine ghostB D 0 (P0 D x) cycle. The statement covers arbitrary mixed charge and energy representatives; P0 idempotence is used only to identify the quotient representative."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-brst-reduction-delta-square"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTZeroEnergyReduction.Delta_square"),
                H("Square-zero of the physical quotient operator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Theorem at native source lines 485--502. For every a : Cohomology D H h26 hHG hGH, with rank D = 26 and both inverse-Gram equations, Delta (Delta a) = 0. The proof reduces through Delta_classOf, uses totalL0 compatibility with B0 and the actual B0 square-zero law, and makes no BV or product assertion."))), DescribeRole.Theorem))));
}
