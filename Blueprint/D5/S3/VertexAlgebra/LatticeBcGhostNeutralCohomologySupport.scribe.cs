using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeBcGhostNeutralCohomologySupportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/LatticeBcGhostNeutralCohomologySupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original lattice bc-BRST state decomposes by charge and energy; for a neutral zero-energy target, full Q-image membership reduces to a preimage in the same sector.",
        H("Original lattice bc-BRST charge and energy support"),
        Blocks(
            Paragraph(Text("The declarations in this unit use the original LatticeData carrier, with arbitrary natural rank, an integral symmetric Gram matrix and even diagonal. The state space is the actual complex tensor product of the lattice oscillator carrier with the algebraic bc Fock space. A basis label is a lattice charge/exponent label together with a finite ghost subset; no positivity, cutoff, finite charge window or nonisotropic restriction is introduced here.")),
            Paragraph(Text("The Support namespace isolates charge-zero states and proves the exact ghost-energy enumeration needed at the zero-energy boundary. The Image namespace uses the full tensor basis to define simultaneous charge and total-energy projections. Under H*gramComplex D=1 and gramComplex D*H=1, its coefficient-blocking results show that the original Q preserves both labels. For a target already neutral and in ker(M D H 0 + G D 0), a full State preimage can therefore be projected to that same sector without replacing Q by a different differential. This does not identify the entire range of Q with the restricted range.")),
            Paragraph(Text("The Energy namespace supplies the all-energy contracting operator. P0 is the total-energy-zero projection, EInv is the inverse energy weight away from zero, and h=(B D 0).comp(EInv D) applies EInv first and then the original B0 action. The homotopy identity and cycle reduction require both Gram inverse equations and no rank-26 premise. They reduce every Q-cycle, at any lattice charge, to a Q-cycle in the total-energy-zero sector, while preserving the original State and Q.")),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-support-state-basis"),
                DeclarationHandle.Create(Prefix + "stateBasis"),
                H("Tensor-product basis for the actual state space"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("stateBasis is the tensor product of the existing lattice carrier basis and the finite-subset ghost basis. It is the coordinate system used by every later charge, energy and projection theorem; it is not a finite truncation of the state space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-support-zero-labels"),
                DeclarationHandle.Create(Prefix + "zeroLabels"),
                H("Exact neutral zero-energy labels"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("zeroLabels records the complete charge-zero, total-energy-zero basis-label list: the four ground ghost subsets and the two one-oscillator families indexed by a lattice axis. This is an exact enumeration in the original infinite algebraic Fock space, not a cutoff statement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-support-oscillator-energy"),
                DeclarationHandle.Create(Prefix + "oscillator_energy_one_iff"),
                H("One-oscillator energy classification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The oscillator energy is one exactly for a single exponent at mode zero. Together with the ghost-energy case split, this theorem supplies the complete one-oscillator part of the neutral zero-energy label classification."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-support-energy-iff"),
                DeclarationHandle.Create(Prefix + "neutral_energy_iff"),
                H("Neutral total-energy zero classification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a neutral lattice label and a finite ghost subset, total energy is zero exactly in the ground or one-oscillator cases recorded by zeroLabels. The statement is derived from the actual lattice and ghost grading and does not assume positivity beyond the imported model facts used in the proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-support-t0-span"),
                DeclarationHandle.Create(Prefix + "neutral_T0_kernel_eq_span"),
                H("Neutral T0 kernel is the native span"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the two-sided Gram inverse hypotheses, the kernel of M D H 0 + G D 0 inside the neutral submodule is exactly the span of the basis labels in zeroLabels. This is the precise zero-energy neutral reduction used by the native basis module."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-image-joint-projection"),
                DeclarationHandle.Create(Prefix + "jointProjection"),
                H("Charge and total-energy projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Image.jointProjection is the coordinate projection onto simultaneous charge-zero and total-energy-zero labels in the full tensor basis. It is defined on the complete State space and is not a projection onto a hand-selected finite subspace."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-image-q-charge-blocks"),
                DeclarationHandle.Create(Prefix + "Q_charge_coeff_zero"),
                H("Q preserves lattice-charge blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary H, a Q image coefficient at a different lattice charge vanishes; this charge-only theorem needs neither Gram inverse equation nor rank 26. The proof uses the actual finite statewise Q expansion and the existing lattice-sector action, so it preserves the original all-charge operator rather than postulating a charge-truncated complex."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-image-projection-commutes"),
                DeclarationHandle.Create(Prefix + "jointProjection_commutes"),
                H("Joint projection commutes with Q"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under both Gram inverse equations, the simultaneous neutral and total-energy projection commutes with the original Q, with no rank-26 premise. This supplies the image-membership bridge for a target already in the neutral T0 kernel; it does not assert equality of the entire full and restricted Q ranges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-image-full-restriction"),
                DeclarationHandle.Create(Prefix + "full_image_iff_restricted"),
                H("Q-image membership for a neutral zero-energy target"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assume H*gramComplex D=1 and gramComplex D*H=1, and let y be a State D already satisfying y ∈ Image.neutral D intersect ker(M D H 0 + G D 0), the same E0 used in the cohomology unit. Then y ∈ range(Q D H) if and only if there exists x : State D in that same neutral T0 kernel with Q D H x=y. The left side allows a preimage anywhere in the full State; the right side requires an E0 preimage. No rank-26 premise occurs. The theorem compares membership only for such y, not the entire range of Q with the restricted range; it does not replace Q by a coordinate differential or assert a physical no-ghost theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-energy-inverse"),
                DeclarationHandle.Create(Prefix + "EInv"),
                H("Inverse away from total energy zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("EInv acts by the reciprocal of the integer total energy away from zero and by zero at energy zero. It is an algebraic spectral inverse on the full basis, not an analytic inverse and not a positivity or cutoff assumption."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-energy-homotopy"),
                DeclarationHandle.Create(Prefix + "homotopy_identity"),
                H("All-energy BRST homotopy identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With both Gram inverse equations, Q*h+h*Q equals 1-P0 on the entire original State space. The proof uses the existing Ward identity for Q and B, the exact energy-block commutation, and the spectral inverse EInv. This is the all-energy neutral reduction mechanism."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticebcghostneutral-energy-cycle-reduction"),
                DeclarationHandle.Create(Prefix + "cycle_reduction"),
                H("Every Q-cycle reduces to zero total energy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under both Gram inverse equations, if x : State D satisfies Q D H x=0, then y=P0 D x is Q-closed, lies in ker(M D H 0 + G D 0), and satisfies x-y=Q D H (h D x). No rank-26 premise is needed. This reduction applies to every lattice charge in the full state space, but does not compute the remaining charged zero-energy cohomology or provide physical state selection or string completion."))),
                DescribeRole.Theorem),
            Paragraph(Text("Reuse and attribution: the carrier, L0, bc-Fock, BRST charge, total covariance and ghost-number operations are imported from the existing D5/S3/VertexAlgebra modules. The declarations here are repository-derived consequences of those actual definitions and proofs. No new positivity, intercept, rank-26, analytic completion or finite cutoff premise is added. The separate native cohomology unit supplies the quotient, inverse, J0/ghost grading and absolute/relative dimensions built on this support.")),
            Paragraph(Text("Boundary: this unit does not close nonzero-charge cohomology, a no-ghost theorem, the full VOA/CFT construction, physical string theory or an AdS/CFT correspondence. Those remain active open goals beyond the formal consequences recorded here."))
        )));
}
