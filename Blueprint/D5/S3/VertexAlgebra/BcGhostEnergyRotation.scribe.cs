using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class BcGhostEnergyRotationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/BcGhostEnergyRotation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full finite-support bc Fock carrier has a real integer conformal-energy half-turn.",
        H("Actual bc ghost conformal-energy half-turn"),
        Blocks(
            Paragraph(Text("For a finite-support ghost state indexed by a finite subset S of the actual mode sites, use the native integer siteWeight and energy(S) = sum siteWeight. The operator rotation is the diagonal finite-support linear operator with coefficient (-1)^energy(S), where the exponent is the integer zpow and may be negative.")),
            Describe.Lean(
                DescribeId.Create("bc-ghost-energy-rotation-involution"),
                DeclarationHandle.Create(Prefix + "rotation_involutive"),
                H("Energy rotation is an involution"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The diagonal phase squares to one on every actual basis state, so rotation composed with itself is the identity on the unrestricted algebraic Fock carrier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-energy-rotation-real"),
                DeclarationHandle.Create(Prefix + "rotation_star_coefficient"),
                H("Energy rotation has real coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complex conjugation fixes every integer power of -1, giving coefficientwise compatibility with the native conjugate-left convention."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-energy-rotation-zero-mode"),
                DeclarationHandle.Create(Prefix + "rotation_commutes_zero"),
                H("Energy rotation commutes with the actual ghost L(0)"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The operator is diagonal in the same unrestricted finite-subset basis as the actual L(0), whose eigenvalue is the native integer energy."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-energy-rotation-b-mode"),
                DeclarationHandle.Create(Prefix + "rotation_b"),
                H("Energy rotation intertwines every b mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual b mode changes the native ghost energy by -mode, including both creator and annihilator branches, so rotation passes through b(mode) with phase (-1)^mode."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bc-ghost-energy-rotation-c-mode"),
                DeclarationHandle.Create(Prefix + "rotation_c"),
                H("Energy rotation intertwines every c mode"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual c mode has the same energy-shift phase law on both creation and annihilation branches; negative integer energies use the genuine integer zpow."))),
                DescribeRole.Theorem),
            Paragraph(Text("This document does not assert the matter oscillator pairing, inverse-Gram Sugawara adjoint, individual A(n) correction, finite symmetric Q cancellation, boundary-cycle orthogonality, quotient descent, charged PCT, or physical no-ghost/isometry conclusions.")))));
}
