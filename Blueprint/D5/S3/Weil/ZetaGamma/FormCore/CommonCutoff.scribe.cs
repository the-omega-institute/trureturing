using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class CommonCutoffDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged.",
        H("Actual Gamma form core: CommonCutoff"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-density"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.density"),
                H("density"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-cutoffkernel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.cutoffKernel"),
                H("cutoffKernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-actual-density-tail-integrable"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.actual_density_tail_integrable"),
                H("actual density tail integrable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-imagekernel"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.imageKernel"),
                H("imageKernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-zerocutoffenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.zeroCutoffEnergy"),
                H("zeroCutoffEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-periodiccutoffenergy"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.periodicCutoffEnergy"),
                H("periodicCutoffEnergy"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-commoncutoff-actual-common-cutoff-integrable-and-identity"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CommonCutoff.actual_common_cutoff_integrable_and_identity"),
                H("actual common cutoff integrable and identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For d>0, real base t, epsilon>0, and only MemLp u 2 on Ioc(t,t+d), both cutoff energies and the full image pairing are integrable and E0_epsilon=Ep_epsilon+B_epsilon. The density tail bound is derived. Canonical PeriodicEnergyTransport definitions own zeroExtension, periodicExtension, windowMeasure and the physical correlations; its weighted lattice/Fubini theorem is instantiated at the actual common cutoff. The sign and coefficient of the boundary pairing are unchanged."))),
                DescribeRole.Theorem))));
}
