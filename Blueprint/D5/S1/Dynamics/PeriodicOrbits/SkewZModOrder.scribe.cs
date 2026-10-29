using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.PeriodicOrbits;

internal sealed class SkewZModOrderDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite cyclic holonomy converts a skew return period into a gcd quotient.",
        H("Finite cyclic holonomy and skew periods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("skew-zmod-order"),
                DeclarationHandle.Create("D5/S1/Dynamics/PeriodicOrbits/SkewZModOrder.skew_minimalPeriod_zmod"),
                H("The gcd formula for a finite cyclic fiber"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an additive skew map over a base self-map f with fiber ZMod q, "
                        + "the return holonomy accumulated over the base minimal period is an "
                        + "element h of ZMod q. The lifted minimal period is the base period "
                        + "multiplied by the additive order of h.")),
                    Paragraph(Text(
                        "When q is nonzero, Mathlib identifies that additive order with "
                        + "q divided by gcd(q,h.val). Thus the theorem exposes the arithmetic "
                        + "content of the group action: a base cycle closes in the fiber after "
                        + "exactly the number of repetitions required to kill its holonomy. "
                        + "The zero holonomy case gives multiplier one, while a nonzero residue "
                        + "can lengthen the orbit by a proper divisor of q."))),
                DescribeRole.Theorem)
        )));
}
