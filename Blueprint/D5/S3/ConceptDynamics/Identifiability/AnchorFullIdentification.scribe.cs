using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identifiability;

internal sealed class AnchorFullIdentificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full anchored identification is equivalent to reachability and injective behavior.",
        H("Anchor Full Identification"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("anchor-full-identification-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Identifiability/AnchorFullIdentification."
                        + "anchor_full_identification_iff"),
                H("Full identification from an anchor"),
                StatementSource.FromAuthor(CriterionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The anchored reachability set is the full state carrier exactly in the "
                            + "first conjunct. Full recovery from the behavior readout is expressed "
                            + "by the library predicate `HasLeftInverse`; its witness is a decoder "
                            + "that recovers every state from its complete behavior.")),
                    Paragraph(Text(
                        "Pinned Mathlib identifies existence of such a decoder with injectivity of "
                            + "the behavior map. The theorem applies that equivalence directly and "
                            + "keeps the independent reachability condition unchanged.")),
                    Paragraph(Text(
                        "If anchored reachability is not the full carrier, the second conjunct "
                            + "exhibits a state outside it. If reachability is full but behavior is "
                            + "not injective, the final conjunct exhibits two reachable, distinct "
                            + "states with the same complete behavior."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula CriterionFormula()
    {
        Formula state = F.Id("X");
        Formula readout = F.Id("Y");
        Formula anchor = F.Id("a");
        Formula reach = F.Id("R");
        Formula behavior = F.Id("beta");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula anchoredReach = Apply(reach, anchor);
        Formula fullReach = Seq(anchoredReach, Sp, Eq, Sp, state);
        Formula leftInverse = Call("HasLeftInverse", behavior);
        Formula injective = Call("Injective", behavior);
        Formula mainCriterion = Seq(
            Open, Open, fullReach, Sp, Land, Sp, leftInverse, Close,
            Sp, Iff, Sp,
            Open, fullReach, Sp, Land, Sp, injective, Close, Close);
        Formula unreachableWitness = Seq(
            Open, anchoredReach, Sp, Neq, Sp, state,
            Sp, Rightarrow, Sp,
            Exists, Sp, x, Colon, Sp, state, Comma, Sp,
            Neg, Sp, x, Sp, InMacro, Sp, anchoredReach, Close);
        Formula indistinguishablePair = Seq(
            Open, fullReach, Sp, Rightarrow, Sp,
            Neg, Sp, injective, Sp, Rightarrow, Sp,
            Exists, Sp, x, Comma, Sp, y, Colon, Sp, state, Comma, Sp,
            x, Sp, InMacro, Sp, anchoredReach, Sp, Land, Sp,
            y, Sp, InMacro, Sp, anchoredReach, Sp, Land, Sp,
            Apply(behavior, x), Sp, Eq, Sp, Apply(behavior, y), Sp, Land, Sp,
            x, Sp, Neq, Sp, y, Close);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, readout, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            anchor, Colon, Sp, state, Comma, Sp,
            reach, Colon, Sp, Arrow(state, Call("Set", state)), Comma, Sp,
            behavior, Colon, Sp, Arrow(state, readout), Comma, Esc,
            mainCriterion, Sp, Land, Esc,
            unreachableWitness, Sp, Land, Esc,
            indistinguishablePair, Dot));
    }
}
