using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Fusion;

internal sealed class StateEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fusion-state entropy equals joint prediction entropy and both Shannon chain-rule forms.",
        H("Fusion State Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fusion-state-entropy-has-both-chain-rule-forms"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Fusion/StateEntropy."
                        + "fusion_state_entropy_identity"),
                H("Fusion-state entropy has both chain-rule forms"),
                StatementSource.FromAuthor(EntropyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let Y be a finite source state space with a nonnegative mass function. "
                            + "The maps pi12, pi1, and pi2 produce the fused and component "
                            + "prediction states, while J maps the fused state into the pair of "
                            + "component states.")),
                    Paragraph(Text(
                        "Assume pi12 is onto, J is injective, and J(pi12(y)) equals "
                            + "(pi1(y), pi2(y)) for every source state. The source-semantic "
                            + "pushforward laws then identify the fused law with the jointly "
                            + "predicted pair law up to the injective relabeling J.")),
                    Paragraph(Text(
                        "Entropy invariance under injective relabeling gives the first equality. "
                            + "Applying the finite Shannon chain rule to the pair law, and then "
                            + "to its coordinate swap, gives the two displayed conditional-"
                            + "entropy decompositions."))),
                DescribeRole.Theorem))));

    private static Formula Push(Formula map, Formula mass) =>
        Call("push", map, mass);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Pair(Formula first, Formula second) =>
        Call("pair", first, second);

    private static Formula Entropy(Formula law) =>
        Call("H", law);

    private static Formula ConditionalEntropy(Formula law) =>
        Call("Hcond", law);

    private static Formula EntropyFormula()
    {
        Formula stateType = F.Id("Y");
        Formula firstType = F.Id("Z1");
        Formula secondType = F.Id("Z2");
        Formula fusedType = F.Id("Z12");
        Formula mass = F.Id("p");
        Formula fused = F.Id("pi12"), first = F.Id("pi1"), second = F.Id("pi2");
        Formula embedding = F.Id("J");
        Formula pair = Pair(first, second);
        Formula fusedLaw = Push(fused, mass);
        Formula pairLaw = Push(pair, mass);
        Formula firstLaw = Push(first, mass);
        Formula secondLaw = Push(second, mass);
        Formula swappedLaw = Call("swap", pairLaw);
        Formula y = F.Id("y");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, stateType, Comma, Sp, firstType, Comma, Sp,
            secondType, Comma, Sp, fusedType, Comma, RowBreak,
            mass, Colon, Sp, stateType, Sp, To, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            fused, Colon, Sp, stateType, Sp, To, Sp, fusedType, Comma, RowBreak,
            first, Colon, Sp, stateType, Sp, To, Sp, firstType, Comma, Sp,
            second, Colon, Sp, stateType, Sp, To, Sp, secondType, Comma, RowBreak,
            embedding, Colon, Sp, fusedType, Sp, To, Sp,
            Seq(firstType, Times, Sp, secondType), Comma, RowBreak,
            Call("nonnegative", mass), Sp, Land, Sp,
            Call("Surjective", fused), Sp, Land, Sp,
            Call("Injective", embedding), Sp, Land, RowBreak,
            Forall, Sp, y, InMacro, Sp, stateType, Comma, Sp,
            Apply(embedding, Apply(fused, y)), Sp, Eq, Sp,
            Apply(Pair(first, second), y), Sp, Rightarrow, RowBreak,
            Entropy(fusedLaw), Sp, Eq, Sp, Entropy(pairLaw), Sp, Land, RowBreak,
            Entropy(fusedLaw), Sp, Eq, Sp,
            Entropy(firstLaw), Sp, Plus, Sp, ConditionalEntropy(pairLaw), Sp, Land, RowBreak,
            Entropy(fusedLaw), Sp, Eq, Sp,
            Entropy(secondLaw), Sp, Plus, Sp, ConditionalEntropy(swappedLaw), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
