using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Dynamics.SpaceTime;

internal sealed class TimeTranslationStabilizerDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Dynamics/SpaceTime/TimeTranslationStabilizer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Time-translation symmetries form a stabilizer subgroup, and symmetry breaking is strict loss of stabilizing parameters.",
        H("Time-Translation Stabilizer"),
        Blocks(
            Def("stabilizer", "timeStabilizer", "Time stabilizer subgroup",
                "The temporal group elements fixing one state form a subgroup."),
            Def("lost", "LostTimeSymmetry", "Lost time symmetry",
                "A temporal parameter fixes the earlier state and moves the later state."),
            Def("break", "TimeSymmetryBreaksFrom", "Time-symmetry breaking",
                "The later stabilizer is contained in the earlier one and at least one earlier symmetry is lost."),
            Thm("membership", "mem_timeStabilizer_iff", "Stabilizer membership is fixedness",
                "A time parameter belongs to the stabilizer exactly when its permutation fixes the state."),
            Thm("witness", "timeSymmetryBreaksFrom_has_witness", "Every break has a lost symmetry",
                "The breaking predicate contains an explicit time-translation witness."),
            Thm("lost-equation", "lostTimeSymmetry_iff", "Lost symmetry as fixed and moved equations",
                "A lost stabilizer is exactly a fixed-before and moved-after pair of equations."),
            Thm("self", "no_timeSymmetryBreaksFrom_self", "No self-breaking",
                "A state cannot strictly lose a stabilizer relative to itself."),
            Thm("all-fixed", "no_timeSymmetryBreaksFrom_of_all_fixed", "Universal fixedness prevents breaking",
                "If all temporal parameters fix both states, no lost symmetry exists."),
            Thm("intro", "timeSymmetryBreaksFrom_intro", "Constructing a time-symmetry break",
                "Stabilizer inclusion together with one fixed-before and moved-after witness proves breaking.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Dynamics/SpaceTime/CommutingSpaceTimeAction")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
