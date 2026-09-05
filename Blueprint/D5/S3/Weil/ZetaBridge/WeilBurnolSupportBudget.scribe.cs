using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilBurnolSupportBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaBridge/WeilBurnolSupportBudget.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Burnol tests have a linear support-radius budget common to every coefficient vector. Positive peak and killer radii are derived from compactness.",
        H("Support Budget of Multi-Orbit Localization"),
        Blocks(
            Describe.Lean(DescribeId.Create("weil-support-convolution-addition"),
                DeclarationHandle.Create(Prefix + "convolve_tsupport_subset_Icc"),
                H("Convolution adds support radii"),
                StatementSource.FromAuthor(Disp(F.Id("supp(f) in [-B,B] and supp(g) in [-K,K] imply supp(f*g) in [-(B+K),B+K]."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use Mathlib support_convolution_subset and closedness of the sum of two compact supports. Add the two endpoint inequalities. This extends the radius-one power argument already used in ConvolutionPowerAmplification."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weil-support-power-radius"),
                DeclarationHandle.Create(Prefix + "convolutionSuccPower_tsupport_subset_Icc"),
                H("The successor power budget"),
                StatementSource.FromAuthor(Disp(F.Id("A test supported in [-B,B] has its (N+1)-fold convolution supported in [-(N+1)B,(N+1)B]."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Induct using the existing successor-power constructor. The zero index means one actual convolution factor, so no compactly supported convolution identity is invented."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weil-support-linear-synthesis"),
                DeclarationHandle.Create(Prefix + "finiteWeilLinearCombination_tsupport_subset_Icc"),
                H("All coefficients share the basis window"),
                StatementSource.FromAuthor(Disp(F.Id("If every basis test is supported in [-L,L], every finite linear combination is supported there."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Outside the interval every summand vanishes. Closedness passes this support containment to the topological support."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weil-support-finite-family-radius"),
                DeclarationHandle.Create(Prefix + "finiteWeilFamily_common_support_radius"),
                H("A positive common radius exists"),
                StatementSource.FromAuthor(Disp(F.Id("For every finite Weil family there exists L>0 containing every topological support."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Compact supports are bounded. Choose positive individual radii and use one plus their finite sum. The construction also handles the empty family."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weil-support-burnol-coefficient-uniform"),
                DeclarationHandle.Create(Prefix + "burnolSynthesis_tsupport_subset"),
                H("Linear support cost of localization"),
                StatementSource.FromAuthor(Disp(F.Id("For all N,a, supp(f_(N,a)) lies in [-L_N,L_N], with L_N=(N+1)B+K."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply the power bound to the common peak, add the killer radius, and then apply the finite synthesis bound. The radius does not depend on a."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("weil-support-burnol-constructed-budget"),
                DeclarationHandle.Create(Prefix + "exists_burnol_linear_support_budget"),
                H("The budget constants come from the actual packet"),
                StatementSource.FromAuthor(Disp(F.Id("There exist B,K>0 bounding the peak and all killers, and L_N=(N+1)B+K bounds every localized synthesis."))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Apply finite-family compactness to the singleton peak family and the actual killer family. The resulting constants depend on the packet. No common radius over all depths or all frames is asserted."))), DescribeRole.Theorem)), []));
}
