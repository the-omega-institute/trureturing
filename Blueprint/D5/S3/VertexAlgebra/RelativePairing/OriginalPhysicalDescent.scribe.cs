using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.RelativePairing;

internal sealed class OriginalPhysicalDescentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/RelativePairing/OriginalPhysicalDescent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual C0 pairing descends in both slots on the literal physical original-Q image.",
        H("Framed on-shell relative ghost-degree-one classes"),
        Blocks(
            Paragraph(Text("Fix an arbitrary LatticeData D and H with H*gram=gram*H=1. Fix beta, an integer level, frame and inverse with both inverse-frame equations, rank 26, a null direction, nonzero chosenP, distinct x/y axes, the x row equal to the null direction and the y row equal to adaptedPartner. Retain both dual-row equations against every frame row and the shell equation chosenH(beta)+level-1=0. The physical cycles are exactly the original Q-cycles in this actual charge/energy sector, annihilated by B D 0 and in actual integer ghost degree one. No positivity, real longitudinal rows, occupation cutoff or alternate carrier is imposed.")),
            Paragraph(Text("physicalBoundaries is the actual OriginalBoundaries comap along the inclusion of physicalCycles into OriginalCycles. Thus PhysicalCohomology identifies precisely states with the same literal original absolute class; it does not impose a smaller relation. inclusion is induced by the actual OriginalBoundaries.mkQ. physicalImage is its range, proved equal to the image of physicalCycles under that same mkQ. imageEquiv identifies the subquotient with this literal subspace of OriginalCohomology.")),
            Describe.Lean(DescribeId.Create("physical-c0-four-representatives"),
                DeclarationHandle.Create(Prefix + "representative_independent"), H("Simultaneous two-slot representative independence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any four physical relative degree-one cycles in the same framed on-shell sector whose original classes agree pairwise, F(first,C0 third)=F(second,C0 fourth). The existing literal_physical_equality_iff_relative_preimage produces relative degree-zero sector preimages of both differences. The actual left and right obstruction laws vanish on those repaired preimages, establishing both changes of representatives simultaneously."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-c0-boundary-kernel"),
                DeclarationHandle.Create(Prefix + "physical_boundary_vanishing"), H("The actual boundary comap annihilates both form slots"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Membership in the actual OriginalBoundaries begins with an unrestricted State preimage. relative_ambient_boundary_homotopy_preimage supplies the same explicit native finite-HPL preimage carrying relativity, ghost degree zero, charge and energy; applying the actual tensor boundary theorem kills both inserted pairings. No unrestricted relative-to-absolute injection is assumed. The existing neutral absolute-exact but relative-nonexact zState is outside the nonzero chosenP scope and remains unchanged."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-c0-inclusion-injective"),
                DeclarationHandle.Create(Prefix + "inclusion_injective"), H("Faithful inclusion of the physical subquotient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel of the restricted actual class map is precisely physicalBoundaries, so its quotient inclusion is injective. This is a first-isomorphism statement for an actual boundary comap, not a claim that every relative boundary relation equals the ambient one in all sectors."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-c0-inclusion-representative"),
                DeclarationHandle.Create(Prefix + "inclusion_mk"), H("The inclusion uses the literal original class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each physical cycle the quotient inclusion is exactly its OriginalBoundaries.mkQ class."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-c0-literal-image"),
                DeclarationHandle.Create(Prefix + "physicalImage_eq"), H("The carrier is the literal physical image"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The range of inclusion equals the actual original class map applied to the full physical cycle submodule."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-c0-quotient-recovery"),
                DeclarationHandle.Create(Prefix + "quotientForm_mk"), H("Exact representative recovery on the physical subquotient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("quotientForm is constructed by the two actual Submodule.liftQ operations, using the established two-slot boundary vanishing. It is conjugate-linear on the left and linear on the right, and on quotient representatives equals the original F(left,C D 0 right), without rescaling or changing the rotation phase."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-c0-image-recovery"),
                DeclarationHandle.Create(Prefix + "imageForm_recovery"), H("Exact representative recovery on the literal image"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("imageForm transports the constructed quotientForm through the proved canonical imageEquiv. On the literal original classes of physical representatives it returns their actual inserted C0 pairing."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-c0-quotient-hermitian"),
                DeclarationHandle.Create(Prefix + "quotientForm_hermitian"), H("Hermitian symmetry from actual odd ghost parity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing integral ghost-degree/parity result makes every degree-one physical representative odd for the actual Pi. Its minus sign cancels the negative C0 transpose in F_C, proving quotientForm(left,right)=star(quotientForm(right,left)). No reality hypothesis on frame rows is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("physical-c0-image-hermitian"),
                DeclarationHandle.Create(Prefix + "imageForm_hermitian"), H("Hermitian form on the literal physical image"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact image form inherits Hermitian symmetry from the physical quotient. Descent and symmetry do not prove positivity, a radical calculation, an isometry, a no-ghost theorem, or complete moonshine, string theory or AdS/CFT realization."))), DescribeRole.Theorem))));
}
