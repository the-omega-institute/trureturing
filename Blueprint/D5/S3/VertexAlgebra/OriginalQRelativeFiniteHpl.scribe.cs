using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalQRelativeFiniteHplDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native relative compatibility of the finite original-Q transfer",
        H("Native original-Q finite factors"),
        Blocks(
            Paragraph(Text("The carrier is the original lattice matter tensor full exterior bc-Fock state space over the complex numbers. E is the existing originalEnergySector for a fixed lattice charge beta and an arbitrary integer level. Its total energy eigenvalue is lambda=chosenH(beta)+level-1. The restriction energyB0 uses the actual B(D,0), the existing chargeProjection_B law and the existing totalZero_B_commutator. It introduces neither a different BRST differential nor a replacement complex.")),
            Paragraph(Text("The existing original_delta_B_zero_anticommutes, original_S_B_zero_anticommutes and original_Kdagger_P_B_zero_commute are restricted to E without changing their original proofs. The original Ward identity becomes q b+b q=lambda times the identity on E. Both inverse Gram equations and both inverse frame equations remain explicit wherever the existing restricted transfer operators use them. The two dual-row equations and nonzero chosenP are explicit conditions for the normalized antighost laws.")),
            Paragraph(Text("On shell lambda=0, both s and e=q-d anticommute with b. Therefore b commutes with the actual correction factor -s e, every natural power of that factor, and the exact finite correction inverse sum over range(2*level.toNat+2). This is a finite sum on the invariant energy subtype; there is no occupation cutoff, infinite convergence argument or assumed compatibility record. The same native factors give anticommutation of b with h=T s, and commutation with the inclusion T p and projection p(1-e h).")),
            Paragraph(Text("Inverse commutation is asserted only on shell. Off shell the Ward scalar cannot be discarded; the proposed identity [b,T]=lambda h is a separate unproved endpoint here. The shell compatibility statements do not themselves require rank 26, nullity or the selected row equalities, because they do not invoke Q squared or the finite inverse action laws. Those hypotheses remain necessary in the downstream original-Q preimage theorem using the actual transfer contraction and mass-shell computation.")),
            Paragraph(Text("This is an algebraic finite homological perturbation application on the original carrier, with no literature novelty claimed. The native neutral degree-two witness remains an ambient-exact, relative-nonexact state by z_absolute_exact and z_relative_nonexact in LatticeBcGhostNeutralCohomology. Nothing here asserts relative-to-absolute injectivity for arbitrary charges. Inserted-C0 pairing descent in either slot, radical, isometry, positivity, physical no-ghost, full string theory and AdS/CFT remain separate obligations.")),
            Describe.Lean(
                DescribeId.Create("originalqrelativefinitehpl-native-sector"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalQRelativeFiniteHpl.original_B0_preserves_energy_sector"),
                H("Actual antighost preserves the fixed charge-energy sector"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same actual B0 preserves both defining equations of originalEnergySector, without Gram, frame or rank assumptions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("originalqrelativefinitehpl-finite-inverse"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalQRelativeFiniteHpl.energy_B0_finite_inverse_commutes_on_shell"),
                H("Exact finite inverse commutes with B0 on shell"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact exponent range is 2*level.toNat+2. Both Gram and frame inverses, both dual rows, nonzero chosenP and the shell equation remain in the native statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("originalqrelativefinitehpl-transfer"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalQRelativeFiniteHpl.energy_B0_transfer_compatibility_on_shell"),
                H("Native homotopy, inclusion and projection compatibility"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The homotopy anticommutes with the same restricted antighost; the inclusion and projection commute with it on the actual energy subtype."))),
                DescribeRole.Theorem))));
}
