using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.WorldModel;

internal sealed class WormholeHolonomyDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/WorldModel/WormholeHolonomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nontrivial round trip through observer bridges is a typed holonomy witness.",
        H("Wormhole Holonomy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("left-inverse-removes-wormhole-holonomy"),
                DeclarationHandle.Create(Prefix + "no_holonomy_of_left_inverse"),
                H("A left-inverse return bridge removes holonomy"),
                StatementSource.FromAuthor(HolonomyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Forward and backward wormholes compose to an endomorphism of the source "
                            + "world. Holonomy at a state means that this round trip does not "
                            + "return the state.")),
                    Paragraph(Text(
                        "If the backward map is a genuine left inverse of the forward map, the "
                            + "round trip is the identity and no state has holonomy.")),
                    Paragraph(Text(
                        "This is a typed transport notion and is not identified with differential-"
                            + "geometric connection holonomy."))),
                DescribeRole.Theorem))));

    private static Formula HolonomyFormula() => Disp(Seq(
        Call("LeftInverse", F.Id("back"), F.Id("forward")),
        Sp, Rightarrow, Sp,
        Call("Not", Call("HasHolonomyAt", F.Id("forward"),
            F.Id("back"), F.Id("x")))));
}
