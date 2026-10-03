using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeOppositeExtremalMapsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetric excursions and opposite extremal maps force oscillation.",
        H("Opposite Extremal Maps"),
        Blocks(
        Describe.Lean(
            DescribeId.Create("mamede-symmetric-excursion-outer-empty"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeOppositeExtremalMaps.symmetric_excursion_outer_empty"),
            H("No two exterior factors around a symmetric excursion"),
            StatementSource.FromAuthor(Disp(Q(
                Call("ReducedConsecutiveSymmetricExcursion", V("n"), V("m"), V("M"),
                    V("p"), V("q")), Land,
                Call("InteriorSupport", V("m"), V("M"), V("p"), V("q")),
                Implies, V("p"), Eq, Call("EmptyWord"), Lor,
                V("q"), Eq, Call("EmptyWord")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let 1<=m<M<=n and let the middle word descend from M to m, then "
                + "ascend from m+1 to M. If p and q contain only generators strictly "
                + "between m and M, and the combined word is reduced and consecutive, "
                + "then p or q is empty. The middle product swaps positions m and M+1 "
                + "and fixes the interior. When both factors are nonempty, consecutiveness "
                + "forces generator M-1 at both boundaries; the two copies commute through "
                + "the middle product and cancel, contradicting reducedness. This is an "
                + "unbounded source theorem. It does not derive the displayed factorization "
                + "from opposite endpoint maps or prove their oscillation consequence."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("mamede-opposite-extremal-maps-oscillation"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeOppositeExtremalMaps.opposite_extremal_maps_oscillation"),
            H("Oscillation from both extremal position maps"),
            StatementSource.FromAuthor(Disp(Q(
                Call("SingletonWord", V("n"), V("sigma"), V("a")), Land,
                Call("AttainedGeneratorExtrema", V("m"), V("M"), V("a")), Land,
                Call("GeneratorInterval", V("n"), V("m"), V("M"), V("a")), Land,
                Call("OppositeExtremalMaps", V("n"), V("m"), V("M"), V("sigma")),
                Implies, Call("Oscillation", V("a"))))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let a be a singletonWord for sigma, so a is reduced and consecutive "
                + "and its product is sigma. Suppose m and M both occur in a, "
                + "1<=m<=M<=n, and every letter k satisfies m<=k<=M. If sigma sends "
                + "position M+1 to m and position m to M+1 simultaneously, then "
                + "oscillation(a). For m=M the word begins at its attained minimum. "
                + "For m<M, exterior fixedness and the guarded strand walk force a "
                + "full descent in a and another full descent in its reverse, hence a "
                + "full ascent in a. Comparing the run prefixes aligns them at m or M; "
                + "the two occurrences of m are not assumed equal. The resulting "
                + "descent-then-ascent or ascent-then-descent excursion has strictly "
                + "interior outer factors. The symmetric-excursion obstruction, with "
                + "generator reflection for the second orientation, makes one factor "
                + "empty. An actual extremal first or last letter then supplies the "
                + "endpoint-oscillation theorem. No oscillation, source shape, exterior "
                + "fixedness, or word endpoint is an input. This is the implication for "
                + "the explicit attained-generator interval, not a global fiber count."))),
            DescribeRole.Theorem))));

    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[items.Length * 2 - 1];
        for (var i = 0; i < items.Length; i++)
        {
            spaced[2 * i] = items[i];
            if (i + 1 < items.Length) spaced[2 * i + 1] = Sp;
        }
        return Seq(spaced);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
}
