using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics;

internal sealed class JumpCocycleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeNode.Create("Hidden-fiber jump legality is exactly cocycle consistency.",
            H("Hidden-Fiber Jump Cocycle"),
            Blocks(
                Describe.Lean(DescribeId.Create("hidden-fiber-jump-cocycle"),
                    DeclarationHandle.Create("D5/S1/Dynamics/JumpCocycle.jump_cocycle"),
                    H("Hidden-fiber jump legality is cocycle consistency"),
                    StatementSource.FromAuthor(Disp(Seq(F.Id("s"), Underscore, Grp(Beta), Eq, F.Id("s"), Underscore, Grp(Alpha), Plus, Iota, Open, F.Id("k"), Underscore, Grp(Alpha, Beta), Close, Comma, Quad, Sp, F.Id("s"), Underscore, Grp(GammaLower), Eq, F.Id("s"), Underscore, Grp(Beta), Plus, Iota, Open, F.Id("k"), Underscore, Grp(Beta, GammaLower), Close, Rightarrow, Sp, Left, Open, F.Id("s"), Underscore, Grp(GammaLower), Eq, F.Id("s"), Underscore, Grp(Alpha), Plus, Iota, Open, F.Id("k"), Underscore, Grp(Alpha, GammaLower), Close, Leftrightarrow, Sp, F.Id("k"), Underscore, Grp(Alpha, GammaLower), Eq, F.Id("k"), Underscore, Grp(Alpha, Beta), Plus, F.Id("k"), Underscore, Grp(Beta, GammaLower), Right, Close))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                                            Paragraph(Text(
                                                "Over a nonempty indexing domain, the visible circle projection is a "
                                                + "surjective additive homomorphism. An additive equivalence "
                                                + "identifies "
                                                + "the product of all p-adic integer fibers with its kernel. Two "
                                                + "realized hidden jumps connect three local lifts. Kernel membership "
                                                + "first forces "
                                                + "all three lifts to have the same visible projection.")),
                                            Paragraph(Text(
                                                "A proposed direct jump is legal when translating the first lift by "
                                                + "that jump reaches the third lift. This endpoint condition is "
                                                + "independent of the cocycle equation. Cancelling the first lift, "
                                                + "applying additivity, "
                                                + "and using injectivity of the kernel equivalence prove that endpoint "
                                                + "legality is equivalent to the pointwise sum of the two intervening "
                                                + "jumps. Any disagreement therefore supplies an explicit endpoint "
                                                + "residual and cannot be a legal motion."))),
                    DescribeRole.Theorem)),
[
                            DocumentEdge.Dependency.Create(
                                GidRef.Create("D5/S1/Phase/Basic")),
                        ]));
}
