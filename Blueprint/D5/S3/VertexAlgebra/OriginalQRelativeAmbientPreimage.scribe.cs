using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalQRelativeAmbientPreimageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous relative preimages in the literal original physical quotient",
        H("Actual framed on-shell physical quotient"),
        Blocks(
            Paragraph(Text("All operators act on the original unrestricted finite-support lattice matter tensor full exterior bc-Fock state space over the complex numbers. Fix beta, an integer level and an actual adapted null frame. Retain H*gram=gram*H=1, inverse*frame=frame*inverse=1, rank 26, nullity of the selected direction, nonzero chosenP, distinct x/y axes, frame(x)=nullDirection, frame(y)=adaptedPartner and both dual-row equations against every frame row. The shell equation is chosenH(beta)+level-1=0. No positive signature, finite occupation, finite-dimensional energy fiber or form-adjoint premise is added.")),
            Paragraph(Text("For x in originalEnergySector with B0 x=0, Q x=0, integral ghost degree r and an arbitrary ambient original-Q preimage, the explicit repaired state is h(x)=energyTransferHomotopy(x). This is the existing finite correction inverse, with exactly 2*level.toNat+2 terms, applied to the existing normalized quartet S. The same returned state lies in the fixed charge-energy subtype, is relative, has ghost degree r-1 and maps to x under the actual original Q. No charge, energy, relative and ghost witnesses are separately selected or recombined.")),
            Paragraph(Text("The ambient boundary sector preimage supplies an E-preimage only to show that the actual perturbed projection of x vanishes. The existing transferred differential mass-shell computation makes Dtr zero on E. The existing chain projection law then gives pi_tr(x)=0. Together with Qx=0, the existing qh+hq=1-i*pi_tr identity proves Q(hx)=x. Relative membership follows from the native on-shell homotopy/B0 anticommutation. Exact integral degree follows directly from the existing J0_S_commutator and J0_finite_correction_inverse_commutator through ghostPart_iff_number, without a new ghost projection or a duplicated ghost-number theorem.")),
            Paragraph(Text("For two relative degree-one cycles in this exact same framed on-shell E-sector, equality of their literal OriginalBoundaries.mkQ classes is equivalent to an actual relative E-preimage of their difference in ghost degree zero. The forward implication applies the explicit repaired homotopy to the difference. The reverse implication is literal range membership in the original Q-image. Neither direction assumes that relative cohomology injects into absolute cohomology; the restricted equality statement follows from the actual factors and homotopy laws.")),
            Paragraph(Text("The nonzero chosenP and full adapted-frame hypotheses are retained; beta nonzero alone is not a replacement for them. At neutral beta=0 and level=1, the existing zState has ghost degree two, is ambient-exact by z_absolute_exact and relative-nonexact by z_relative_nonexact. Its existing proofs and statement remain unchanged. There is no all-charge, all-degree ambient-to-relative repair claim and no new bind-only counterexample package.")),
            Paragraph(Text("These are algebraic consequences of the original finite transfer, with no literature novelty asserted. Inserted-C0 physical form descent in both slots, representative independence of that form, its radical, isometry, positivity and physical no-ghost are not consequences of quotient equality alone and remain separate obligations. Absolute tensor forms and Q adjoints are not premises here. Full moonshine, VOA/CFT/anomaly/fusion realization, complete string theory and AdS/CFT remain open.")),
            Describe.Lean(
                DescribeId.Create("originalqrelativeambientpreimage-simultaneous"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalQRelativeAmbientPreimage.relative_ambient_boundary_homotopy_preimage"),
                H("One explicit native preimage has all simultaneous properties"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The preimage is the actual energyTransferHomotopy applied to the input state; its charge and energy are guaranteed by the very same originalEnergySector subtype, and its relative, integer-degree and Q-image properties are proved together."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("originalqrelativeambientpreimage-literal-equality"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalQRelativeAmbientPreimage.literal_physical_equality_iff_relative_preimage"),
                H("Literal physical quotient equality iff a relative degree-zero preimage exists"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The quotient is literally OriginalCycles divided by OriginalBoundaries for the actual original Q, not an abstract transported or replacement quotient. All Gram, frame, shell, critical-rank and homogeneous-cycle conditions remain explicit."))),
                DescribeRole.Theorem))));
}
