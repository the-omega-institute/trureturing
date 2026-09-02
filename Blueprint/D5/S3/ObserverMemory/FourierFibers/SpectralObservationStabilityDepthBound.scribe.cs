using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.FourierFibers;

internal sealed class SpectralObservationStabilityDepthBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A separated finite diagonal spectrum stabilizes the canonical observer "
            + "by the last required Vandermonde sample.",
        H("Spectral Observation Stability-Depth Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("spectral-observation-stability-depth-le"),
                DeclarationHandle.Create("D5/S3/ObserverMemory/FourierFibers/SpectralObservationStabilityDepthBound.spectral_observation_stability_depth_le"),
                H("Finite mode separation bounds canonical stability depth"),
                StatementSource.FromAuthor(DepthBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For depth plus one pairwise distinct modes, the canonical future word through that depth is injective and its observation relation has already stabilized.")),
                    Paragraph(Text(
                        "The theorem reuses observationStabilityDepth, futureReadoutWord, and finite Vandermonde tomography rather than defining a second temporal depth."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula DepthBoundFormula() => Disp(Seq(
        Forall, Sp, F.Id("m"), Comma, Sp, F.Id("d"), Comma, Sp,
        Call("Injective", F.Id("m")), Sp, Rightarrow, Sp,
        Call("observationStabilityDepth",
            Call("oneStepSpectralUpdate", F.Id("m")),
            Call("modalSumReadout")),
        Sp, Leq, Sp, F.Id("d"), Dot));

}
