using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeDualCosetEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational Coset Energy Bounds and an Attained Minimum",
        H("Rational Coset Energy Bounds and an Attained Minimum"),
        Blocks(
            Paragraph(Text("For arbitrary rational mu, q_mu(gamma)=(gamma+mu)^T G (gamma+mu)/2 and weight(gamma,d)=oscillatorEnergy(d)+q_mu(gamma). Positive definiteness is imposed only on the original real Gram matrix. A common positive denominator s and integral nu with s mu=nu give the injective map gamma -> s gamma+nu and the exact identity q_mu(gamma)=chargeEnergy(s gamma+nu)/s^2. Existing integral charge sublevels and oscillator sublevels give all rational finite sublevels and exact finite fibers. Minimizing on the nonempty finite sublevel below q_mu(0) constructs an attained nonnegative GLOBAL minimum; no minimizer is assumed and no uniqueness is claimed. These arithmetic statements do not need beta, duality or inverse-Gram data.")),
            Paragraph(Text("Classical construction context: Bakalov-Kac, math/0402315v1, section 4.1. The imported Sugawara architecture retains Kalle Kytola's Apache-2.0 attribution and VirasoroProject revision 5ff4245383b2cdd4eea7a0524bc1274c32041eb4. The finite reductions and actual-action connections are native mathematical proofs; no external novelty is asserted.")),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-pairing"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.pairing"),
                H("pairing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-chargeWeight"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.chargeWeight"),
                H("chargeWeight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-weight"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.weight"),
                H("weight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-common-denominator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.common_denominator"),
                H("common denominator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-clearedCharge"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.clearedCharge"),
                H("clearedCharge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-clearedCharge-injective"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.clearedCharge_injective"),
                H("clearedCharge injective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-chargeWeight-cleared"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.chargeWeight_cleared"),
                H("chargeWeight cleared"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-chargeWeight-nonneg"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.chargeWeight_nonneg"),
                H("chargeWeight nonneg"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-charge-sublevel-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.charge_sublevel_finite"),
                H("charge sublevel finite"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-sublevel-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.sublevel_finite"),
                H("sublevel finite"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-attained-minimum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.attained_minimum"),
                H("attained minimum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticedualcosetenergy-fiber-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeDualCosetEnergy.fiber_finite"),
                H("fiber finite"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact declaration below uses the objects and hypotheses stated above."))),
                DescribeRole.Theorem))));
}
