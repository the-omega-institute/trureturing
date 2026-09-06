using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.GroundMode;

internal sealed class RealTransverseReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Candidate source; Lean elaboration and Scribe emission are not claimed.",
        H("RealTransverseReadout"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("realtransversereadout-kernelVector"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealTransverseReadout.kernelVector"),
                H("kernelVector"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Construct a continuous kernel as an actual real L2 element using Mathlib ContinuousMap.toLp on a compact finite-measure space."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("realtransversereadout-kernelVector-inner"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealTransverseReadout.kernelVector_inner"),
                H("kernelVector inner"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use Mathlib L2.inner_def and the almost-everywhere identity of ContinuousMap.toLp to identify the actual integral readout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realtransversereadout-kernelVector-gram"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealTransverseReadout.kernelVector_gram"),
                H("kernelVector gram"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The mixed Gram is the full product integral of the two continuous kernels, not a finite Fourier truncation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realtransversereadout-kernelVector-norm-sq"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealTransverseReadout.kernelVector_norm_sq"),
                H("kernelVector norm sq"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Specialize the mixed Gram identity to the same kernel. This supplies the actual squared norm through an integral."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realtransversereadout-real-readout-lower"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealTransverseReadout.real_readout_lower"),
                H("real readout lower"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Cauchy-Schwarz bounds the real error readout and retains its sign to obtain a candidate floor minus an error budget."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("realtransversereadout-transverse-region-nonvanishing"),
                DeclarationHandle.Create("D5/S3/Weil/GroundMode/RealTransverseReadout.transverse_region_nonvanishing"),
                H("transverse region nonvanishing"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Factor the nonzero ordinate from the actual imaginary-readout identity, apply the uniform real-kernel margin and obtain a quantitative bound throughout the declared region. The kernel identity, candidate floor and kernel norm are explicit inputs. The interval consumer supplies finite-box floors, while its elementary Fourier kernel and norm specialization remain paper analysis, not kernel-checked facts."))),
                DescribeRole.Theorem))));
}
