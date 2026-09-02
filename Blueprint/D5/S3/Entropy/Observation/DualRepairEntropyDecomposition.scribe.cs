using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class DualRepairEntropyDecompositionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Observation/DualRepairEntropyDecomposition."
            + "dual_repair_entropy_decomposition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Canonical predictive-interior and forgetting-closure quotients split conditional "
            + "entropy into the two repair costs.",
        H("Dual Repair Entropy Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("dual-repair-conditional-entropy-decomposition"),
                DeclarationHandle.Create(Declaration),
                H("Conditional entropy telescopes across both canonical repairs"),
                StatementSource.FromAuthor(DecompositionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let X be finite, let F update X, let R be an equivalence relation, "
                            + "and let mu be a normalized law with positive mass at every state. "
                            + "The predictive interior and forgetting closure are the imported "
                            + "canonical congruence repairs.")),
                    Paragraph(Text(
                        "Their inclusion proofs induce canonical quotient maps from X/I to X/R "
                            + "and from X/R to X/C. The displayed laws are deterministic "
                            + "pushforwards of mu along these quotient maps, so no entropy target "
                            + "is used to define a source object.")),
                    Paragraph(Text(
                        "Applying the repository quotient-fiber entropy decomposition to I to C, "
                            + "I to R, and R to C gives three entropy balances. Pushforward "
                            + "composition identifies the two closure laws, and the balances "
                            + "telescope to the claimed equality.")),
                    Paragraph(Text(
                        "Pinned Mathlib and installed-package searches found no finite "
                            + "real-valued conditional-entropy theorem with these canonical "
                            + "repair quotients."))),
                DescribeRole.Theorem))));

    private static Formula Sub(Formula value, Formula index) =>
        new Formula.Subscript(value, index);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Pair(Formula first, Formula second) =>
        Seq(Open, first, Comma, Sp, second, Close);

    private static Formula Push(Formula map, Formula law) => Call("pushforward", map, law);

    private static Formula ConditionalEntropy(Formula law) => Call("Hcond", law);

    private static Formula DecompositionFormula()
    {
        Formula state = F.Id("X");
        Formula update = F.Id("F");
        Formula relation = F.Id("R");
        Formula mass = F.Id("mu");
        Formula x = F.Id("x");
        Formula interiorClass = F.Id("i");
        Formula relationClass = F.Id("r");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula interior = Call("congruenceInterior", update, relation);
        Formula closure = Call("congruenceClosure", update, relation);
        Formula interiorQuotient = Sub(F.Id("Q"), F.Id("I"));
        Formula relationQuotient = Sub(F.Id("Q"), F.Id("R"));
        Formula closureQuotient = Sub(F.Id("Q"), F.Id("C"));
        Formula interiorToRelation = Sub(F.Id("pi"), F.Id("IR"));
        Formula relationToClosure = Sub(F.Id("pi"), F.Id("RC"));
        Formula interiorProjection = Sub(F.Id("q"), F.Id("I"));
        Formula interiorLaw = Sub(F.Id("mu"), F.Id("I"));
        Formula relationLaw = Sub(F.Id("mu"), F.Id("R"));
        Formula interiorFintype = Sub(F.Id("f"), F.Id("I"));
        Formula relationFintype = Sub(F.Id("f"), F.Id("R"));
        Formula closureFintype = Sub(F.Id("f"), F.Id("C"));
        Formula fullSupport = Seq(
            Open, Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            D(0), Sp, Lt, Sp, Apply(mass, x), Close);
        Formula normalized = Seq(
            Sum, Underscore, Grp(Seq(x, Colon, Sp, state)), Apply(mass, x),
            Sp, Eq, Sp, D(1));
        Formula mapIR = Call(
            "QuotientMap", F.Id("id"), Seq(interior, Sp, Subseteq, Sp, relation));
        Formula mapRC = Call(
            "QuotientMap", F.Id("id"), Seq(relation, Sp, Subseteq, Sp, closure));
        Formula projectI = Seq(
            Open, x, Sp, Mapsto, Sp, Call("QuotientMk", interior, x), Close);
        Formula nameMap = Seq(
            Open, interiorClass, Sp, Mapsto, Sp,
            Pair(
                Apply(relationToClosure, Apply(interiorToRelation, interiorClass)),
                interiorClass), Close);
        Formula forgettingMap = Seq(
            Open, relationClass, Sp, Mapsto, Sp,
            Pair(Apply(relationToClosure, relationClass), relationClass), Close);
        Formula predictionMap = Seq(
            Open, interiorClass, Sp, Mapsto, Sp,
            Pair(Apply(interiorToRelation, interiorClass), interiorClass), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, state, Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            update, Colon, Sp, state, Sp, To, Sp, state, Comma, Sp,
            relation, Colon, Sp, Call("Setoid", state), Comma, Sp,
            mass, Colon, Sp, state, Sp, To, Sp, real, Comma, RowBreak, Grp(),
            Call("Fintype", state), Sp, Land, Sp, fullSupport, Sp, Land, Sp,
            normalized, Sp, Rightarrow, RowBreak, Grp(),
            F.Id("I"), Sp, Colon, Eq, Sp, interior, Comma, Sp,
            F.Id("C"), Sp, Colon, Eq, Sp, closure, Comma, RowBreak, Grp(),
            interiorQuotient, Sp, Colon, Eq, Sp, Call("Quotient", interior), Comma, Sp,
            relationQuotient, Sp, Colon, Eq, Sp, Call("Quotient", relation), Comma,
            RowBreak, Grp(),
            closureQuotient, Sp, Colon, Eq, Sp, Call("Quotient", closure), Comma,
            RowBreak, Grp(),
            interiorFintype, Sp, Colon, Eq, Sp,
            Call("FintypeOfFinite", interiorQuotient), Comma, Sp,
            relationFintype, Sp, Colon, Eq, Sp,
            Call("FintypeOfFinite", relationQuotient), Comma, RowBreak, Grp(),
            closureFintype, Sp, Colon, Eq, Sp,
            Call("FintypeOfFinite", closureQuotient), Comma, RowBreak, Grp(),
            interiorToRelation, Colon, Sp, interiorQuotient, Sp, To, Sp,
            relationQuotient, Sp, Colon, Eq, Sp, mapIR, Comma, RowBreak, Grp(),
            relationToClosure, Colon, Sp, relationQuotient, Sp, To, Sp,
            closureQuotient, Sp, Colon, Eq, Sp, mapRC, Comma, RowBreak, Grp(),
            interiorProjection, Colon, Sp, state, Sp, To, Sp, interiorQuotient,
            Sp, Colon, Eq, Sp, projectI, Comma, RowBreak, Grp(),
            interiorLaw, Sp, Colon, Eq, Sp, Push(interiorProjection, mass), Comma, Sp,
            relationLaw, Sp, Colon, Eq, Sp,
            Push(interiorToRelation, interiorLaw), Comma, RowBreak, Grp(),
            ConditionalEntropy(Push(nameMap, interiorLaw)), Sp, Eq, Sp,
            ConditionalEntropy(Push(forgettingMap, relationLaw)), Sp, Plus, Sp,
            ConditionalEntropy(Push(predictionMap, interiorLaw)), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }
}
