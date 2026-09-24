using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class CompositionZeroFreeCollarDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/AnalyticClosure/Polylogarithm/CompositionZeroFreeCollar.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive Xu--Zhao composition has an actual normalized slit continuation "
        + "that is analytic on the source domain and zero-free past the unit circle.",
        H("CompositionZeroFreeCollar"), Blocks(
            Describe.Lean(DescribeId.Create("actual-normalized-continuation"),
                DeclarationHandle.Create(Prefix + "normalizedContinuation"),
                H("The actual depth-normalized continuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text(
                    "For a positive head and positive-entry tail, normalizedContinuation uses "
                    + "CompositionDisk.normalized at zero. Away from zero it is the actual "
                    + "CompositionContinuation.continued branch for head :: tail, divided by z "
                    + "to CompositionDisk.depth tail. This removes exactly the source zero order "
                    + "without replacing the source branch by a surrogate."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-zero-free-collar"),
                DeclarationHandle.Create(Prefix + "result"),
                H("An actual zero-free collar past the unit disk"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(
                    Paragraph(Text(
                        "For every head : PNat and tail : List PNat, result proves that "
                        + "normalizedContinuation agrees with CompositionDisk.normalized at every "
                        + "point of norm less than one and is AnalyticOnNhd on the full source slit "
                        + "domain CompositionContinuation.omega. It then supplies one real R0>1, "
                        + "depending on that composition, such that the actual normalized "
                        + "continuation is nonzero at every z in omega with norm less than R0.")),
                    Paragraph(Text(
                        "The unit-circle step follows the actual continued branch along each radial "
                        + "segment. For H(r)=norm(F(r)) squared, the derivative is "
                        + "2/r times norm(F(r)) squared times the real part of the source "
                        + "logarithmic derivative, so CompositionZeroFree.result makes H strictly "
                        + "increase from the nonzero interior value. This avoids an endpoint "
                        + "logarithm and proves nonvanishing on the part of the unit circle lying in "
                        + "omega.")),
                    Paragraph(Text(
                        "CompositionBanks.result at ell=1 supplies the missing actual-branch patch "
                        + "in a closed ball about one. The open zero-free locus in omega, united with "
                        + "that Banks ball, contains the closed unit disk. Compact thickening gives "
                        + "a positive delta whose thickened disk stays in this union, and R0=1+delta "
                        + "closes the collar. The radius is local and composition-dependent: the "
                        + "theorem asserts neither global slit-domain nonvanishing nor a radius "
                        + "uniform over compositions. It does not identify Taylor coefficients with "
                        + "the formal inverse, transfer the contour sign, or assemble the all-j and "
                        + "all-ell inequalities. Xu--Zhao Conjecture 1.3 therefore remains open, "
                        + "with zero solved-problem credit and no novelty or priority claim."))),
                DescribeRole.Theorem))));
}
