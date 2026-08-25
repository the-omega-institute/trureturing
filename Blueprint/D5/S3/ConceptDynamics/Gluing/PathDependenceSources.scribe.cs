using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Gluing;

internal sealed class PathDependenceSourcesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Word order and transition incompatibility independently produce path dependence.",
        H("Two Sources of Path Dependence"),
        Blocks(Describe.Lean(
            DescribeId.Create("path-dependence-has-two-sources"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Gluing/PathDependenceSources."
                    + "path_dependence_has_two_sources"),
            H("Word order and gluing supply independent residuals"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The first witness uses one global product carrier Unit x Bool. Its two "
                        + "actions are applied by the canonical finite-word evaluator, and "
                        + "reversing the two-letter word changes the resulting state.")),
                Paragraph(Text(
                    "The second witness uses the powerset of Bool. Adding false and adding "
                        + "true are distinct bundled closure operators and commute locally. "
                        + "The Boolean swap induces a bijective order isomorphism on sets, "
                        + "but it does not intertwine the add-false closure."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula boolType = F.Id("Bool");
        Formula setBool = Call("Set", boolType);
        Formula carrier = Call("Prod", F.Id("Unit"), boolType);
        Formula update = F.Id("u");
        Formula action = F.Id("a");
        Formula bit = F.Id("b");
        Formula state = Call("pair", F.Id("star"), bit);
        Formula updatedBit = Call("if", action, F.Id("false"), Call("not", bit));
        Formula updatedState = Call("pair", F.Id("star"), updatedBit);
        Formula start = Call("pair", F.Id("star"), F.Id("false"));
        Formula addFalse = F.Id("addFalse");
        Formula addTrue = F.Id("addTrue");
        Formula transition = F.Id("transition");
        Formula set = F.Id("S");
        Formula empty = F.Id("empty");

        return Disp(new Formula.Aligned([
            Seq(update, Colon, Sp, boolType, Sp, To, Sp, carrier, Sp, To, Sp, carrier,
                Comma),
            Seq(Call("apply", update, action, state), Sp, Eq, Sp, updatedState, Comma),
            Seq(
                Call("Run", update,
                    Call("word", F.Id("false"), F.Id("true")), start), Sp, Neq, Sp,
                Call("Run", update,
                    Call("word", F.Id("true"), F.Id("false")), start), Comma),
            Seq(
                addFalse, Comma, Sp, addTrue, Colon, Sp,
                Call("ClosureOperator", setBool), Comma, Sp,
                transition, Colon, Sp, Call("OrderIso", setBool, setBool), Comma),
            Seq(
                Call("apply", addFalse, set), Sp, Eq, Sp,
                Call("union", set, Call("singleton", F.Id("false"))), Comma, Sp,
                Call("apply", addTrue, set), Sp, Eq, Sp,
                Call("union", set, Call("singleton", F.Id("true"))), Comma),
            Seq(
                Call("apply", transition, set), Sp, Eq, Sp,
                Call("image", Call("swap", F.Id("false"), F.Id("true")), set),
                Comma),
            Seq(
                Call("Commute", addFalse, addTrue), Sp, Land, Sp,
                Call("apply", transition, Call("apply", addFalse, empty)), Sp, Neq, Sp,
                Call("apply", addFalse, Call("apply", transition, empty)), Dot),
        ]));
    }
}
