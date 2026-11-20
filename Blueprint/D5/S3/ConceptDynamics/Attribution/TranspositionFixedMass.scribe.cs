using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class TranspositionFixedMassDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/TranspositionFixedMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp mass fixed by a transposition for paired labels and two-element subsets.",
        H("A transposition bound from two readouts"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("seeded-transposition-mass-bound"),
                DeclarationHandle.Create(Prefix + "seeded_transposition_mass_le"),
                H("The mass fixed by a transposition is at most one sixth"),
                StatementSource.FromAuthor(Bound()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A finite seed set carries an action of the group of permutations of four "
                        + "labels. The weights are nonnegative, total one, and invariant. Each seed is read "
                        + "as a label and as a two-element subset of labels, with both readouts equivariant. "
                        + "FixedMass sums the weights of seeds fixed by the transposition of labels zero and one.")),
                    Paragraph(Text("For every label and two-element subset exactly one of the six transpositions "
                        + "fixes both. Conjugacy and invariance give each transposition the same mass among "
                        + "the readout pairs. Every fixed seed contributes to that transposition's fixed "
                        + "readout mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("uniform-label-and-pair-attainment"),
                DeclarationHandle.Create(Prefix + "uniform_label_pair_attains"),
                H("The uniform label-and-pair law attains the bound"),
                StatementSource.FromAuthor(Attainment()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The invariant law assigns positive mass to every label and two-element subset "
                        + "pair and zero elsewhere. The label marginal has mass one quarter per label and the subset "
                        + "marginal has mass one sixth per two-element subset. The total mass is one. The fixed "
                        + "mass is one sixth."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Bound()
    {
        Formula s = F.Id("S");
        Formula w = F.Id("w");
        Formula f = F.Id("f");
        Formula g = F.Id("g");
        return Disp(Seq(Forall, Sp, s, Sp, w, Sp, f, Sp, g, Comma, Sp,
            Call("InvariantSeedWeights", s, w), Sp, Land, Sp,
            Call("EquivariantLabelAndPair", s, f, g), Sp, Rightarrow, Sp,
            Call("FixedMass", w, Call("Swap", D(0), D(1))), Sp, Le, Sp, Seq(Frac, Grp(D(1)), Grp(D(6)))));
    }

    private static Formula Attainment()
    {
        Formula w = F.Id("w");
        return Disp(Seq(Exists, Sp, w, Comma, Sp, Call("PositiveExactlyOnLabelAndPair", w),
            Sp, Land, Sp, Call("Invariant", w), Sp, Land, Sp,
            Call("UniformLabelMarginal", w, Seq(Frac, Grp(D(1)), Grp(D(4)))), Sp, Land, Sp,
            Call("UniformPairMarginal", w, Seq(Frac, Grp(D(1)), Grp(D(6)))), Sp, Land, Sp,
            Call("TotalMass", w), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Call("FixedMass", w, Call("Swap", D(0), D(1))), Sp, Eq, Sp, Seq(Frac, Grp(D(1)), Grp(D(6)))));
    }
}
