using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class TargetContinuityFactorizationDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On an inhabited source, recoverability is continuity into the discrete "
            + "target.",
        H("Target Continuity Factorization"),
        Blocks(Describe.Lean(
            DescribeId.Create("target-factorization-is-partition-continuity"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/ObservationTopology/TargetContinuityFactorization."
                    + "target_factors_iff_continuous_partition"),
            H("Target recovery is continuity from the partition topology"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Refines target readout means that a recovery map reconstructs the target "
                        + "from the displayed readout.")),
                Paragraph(Text(
                    "Such a factorization makes the target constant on every readout fiber. "
                        + "Conversely, inhabitedness and the target recovery criterion turn "
                        + "fiber constancy into a recovery factor.")),
                Paragraph(Text(
                    "For the partition topology on the source and the bottom topology on the "
                        + "target, continuity is exactly that same fiber-constancy law.")),
                Paragraph(Text(
                    "The displayed biconditional therefore retains the Lean theorem's "
                        + "Nonempty source hypothesis and its discrete target topology."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula coordinate = F.Id("Coordinate");
        Formula targetOutput = F.Id("Target");
        Formula readout = F.Id("readout");
        Formula target = F.Id("target");
        Formula continuity = Call(
            "Continuous",
            Call("partitionTopology", readout),
            Call("bottomTopology", targetOutput),
            target);
        Formula conclusion = Seq(
            Call("Refines", target, readout), Sp, Iff, Sp, continuity);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, readout, Colon, Sp, Call("Concept", state, coordinate),
            Comma, Sp,
            target, Colon, Sp, Call("Concept", state, targetOutput), Comma,
            RowBreak, Grp(),
            Call("Nonempty", state), Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusion, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
