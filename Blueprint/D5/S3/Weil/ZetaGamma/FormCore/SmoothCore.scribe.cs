using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class SmoothCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For real a, an L2 profile u on (-a,a] and finite directionalEnergy(actualGammaExitMeasure,F), where F is its literal Ioc zero extension, inward cutoff and bump convolution give smooth compact approximation supported inside (-a,a). The sum of physical squared mass error and directional energy error is less than each prescribed positive epsilon. The mass can equivalently be written on the source interval using coreL2Mass_error_eq_original_ioc. For a>0, finite integral of DomainPassage.zeroEnergyDensity also supplies the required finite directional energy: take the measurable AE representative G, preserve each translated squared gap by AE equality, and apply lintegral_withDensity_eq_lintegral_mul. Since each translated gap is integrable by MemLp 2 and the density is nonnegative on Ioi 0, the resulting directional energy is ofReal(integral_Ioi0 zeroEnergyDensity). The epsilon/8 error budget and AE congruence preserve the original endpoint jumps. No evenness is required.",
        H("Actual Gamma form core: SmoothCore"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcore-coregraphsize"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCore.coreGraphSize"),
                H("coreGraphSize"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a, an L2 profile u on (-a,a] and finite directionalEnergy(actualGammaExitMeasure,F), where F is its literal Ioc zero extension, inward cutoff and bump convolution give smooth compact approximation supported inside (-a,a). The sum of physical squared mass error and directional energy error is less than each prescribed positive epsilon. The mass can equivalently be written on the source interval using coreL2Mass_error_eq_original_ioc. For a>0, finite integral of DomainPassage.zeroEnergyDensity also supplies the required finite directional energy: take the measurable AE representative G, preserve each translated squared gap by AE equality, and apply lintegral_withDensity_eq_lintegral_mul. Since each translated gap is integrable by MemLp 2 and the density is nonnegative on Ioi 0, the resulting directional energy is ofReal(integral_Ioi0 zeroEnergyDensity). The epsilon/8 error budget and AE congruence preserve the original endpoint jumps. No evenness is required."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcore-coregraphsize-add-le"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCore.coreGraphSize_add_le"),
                H("coreGraphSize add le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a, an L2 profile u on (-a,a] and finite directionalEnergy(actualGammaExitMeasure,F), where F is its literal Ioc zero extension, inward cutoff and bump convolution give smooth compact approximation supported inside (-a,a). The sum of physical squared mass error and directional energy error is less than each prescribed positive epsilon. The mass can equivalently be written on the source interval using coreL2Mass_error_eq_original_ioc. For a>0, finite integral of DomainPassage.zeroEnergyDensity also supplies the required finite directional energy: take the measurable AE representative G, preserve each translated squared gap by AE equality, and apply lintegral_withDensity_eq_lintegral_mul. Since each translated gap is integrable by MemLp 2 and the density is nonnegative on Ioi 0, the resulting directional energy is ofReal(integral_Ioi0 zeroEnergyDensity). The epsilon/8 error budget and AE congruence preserve the original endpoint jumps. No evenness is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcore-coregraphsize-congr-ae"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCore.coreGraphSize_congr_ae"),
                H("coreGraphSize congr ae"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a, an L2 profile u on (-a,a] and finite directionalEnergy(actualGammaExitMeasure,F), where F is its literal Ioc zero extension, inward cutoff and bump convolution give smooth compact approximation supported inside (-a,a). The sum of physical squared mass error and directional energy error is less than each prescribed positive epsilon. The mass can equivalently be written on the source interval using coreL2Mass_error_eq_original_ioc. For a>0, finite integral of DomainPassage.zeroEnergyDensity also supplies the required finite directional energy: take the measurable AE representative G, preserve each translated squared gap by AE equality, and apply lintegral_withDensity_eq_lintegral_mul. Since each translated gap is integrable by MemLp 2 and the density is nonnegative on Ioi 0, the resulting directional energy is ofReal(integral_Ioi0 zeroEnergyDensity). The epsilon/8 error budget and AE congruence preserve the original endpoint jumps. No evenness is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcore-actual-ioc-exists-smooth-compact-core-approximation"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCore.actual_ioc_exists_smooth_compact_core_approximation"),
                H("actual ioc exists smooth compact core approximation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a, an L2 profile u on (-a,a] and finite directionalEnergy(actualGammaExitMeasure,F), where F is its literal Ioc zero extension, inward cutoff and bump convolution give smooth compact approximation supported inside (-a,a). The sum of physical squared mass error and directional energy error is less than each prescribed positive epsilon. The mass can equivalently be written on the source interval using coreL2Mass_error_eq_original_ioc. For a>0, finite integral of DomainPassage.zeroEnergyDensity also supplies the required finite directional energy: take the measurable AE representative G, preserve each translated squared gap by AE equality, and apply lintegral_withDensity_eq_lintegral_mul. Since each translated gap is integrable by MemLp 2 and the density is nonnegative on Ioi 0, the resulting directional energy is ofReal(integral_Ioi0 zeroEnergyDensity). The epsilon/8 error budget and AE congruence preserve the original endpoint jumps. No evenness is required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-smoothcore-corel2mass-error-eq-original-ioc"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/SmoothCore.coreL2Mass_error_eq_original_ioc"),
                H("coreL2Mass error eq original ioc"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a, an L2 profile u on (-a,a] and finite directionalEnergy(actualGammaExitMeasure,F), where F is its literal Ioc zero extension, inward cutoff and bump convolution give smooth compact approximation supported inside (-a,a). The sum of physical squared mass error and directional energy error is less than each prescribed positive epsilon. The mass can equivalently be written on the source interval using coreL2Mass_error_eq_original_ioc. For a>0, finite integral of DomainPassage.zeroEnergyDensity also supplies the required finite directional energy: take the measurable AE representative G, preserve each translated squared gap by AE equality, and apply lintegral_withDensity_eq_lintegral_mul. Since each translated gap is integrable by MemLp 2 and the density is nonnegative on Ioi 0, the resulting directional energy is ofReal(integral_Ioi0 zeroEnergyDensity). The epsilon/8 error budget and AE congruence preserve the original endpoint jumps. No evenness is required."))),
                DescribeRole.Theorem))));
}
