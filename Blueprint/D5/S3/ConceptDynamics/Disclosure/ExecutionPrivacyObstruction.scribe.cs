using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Disclosure;

internal sealed class ExecutionPrivacyObstructionDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Disclosure/ExecutionPrivacyObstruction."
            + "execution_privacy_obstruction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonpublic target-sensitive core obstructs exact execution without new leakage.",
        H("Execution-Privacy Obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("execution-privacy-obstruction"),
            DeclarationHandle.Create(Declaration),
            H("Execution and zero new leakage are incompatible"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The forced part is explicitly the meet of the target and sensitive "
                        + "readouts, while the prior leak is the before component named by the "
                        + "canonical structural no-new-leak predicate.")),
                Paragraph(Text(
                    "Exact realization and structural no-new-leak would force the sensitive "
                        + "part below the prior leak, contradicting the displayed obstruction "
                        + "premise."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula TheoremFormula()
    {
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula state = F.Id("X");
        Formula publicType = F.Id("P");
        Formula addedType = F.Id("L");
        Formula sensitiveType = F.Id("S");
        Formula targetType = F.Id("E");
        Formula forcedType = F.Id("K");
        Formula beforeType = F.Id("Before");
        Formula afterType = F.Id("After");
        Formula publicConcept = F.Id("p");
        Formula added = F.Id("l");
        Formula sensitive = F.Id("s");
        Formula target = F.Id("e");
        Formula forcedPart = F.Id("k");
        Formula before = F.Id("before");
        Formula after = F.Id("after");
        Formula join = Call("conceptJoin", publicConcept, added);
        Formula obstruction = And(
            Call("IsConceptMeet", target, sensitive, forcedPart),
            new Formula.Not(Call("Refines", forcedPart, before)));
        Formula simultaneous = And(
            Call("Refines", target, join),
            Call("StructurallyNoNewLeak",
                publicConcept, added, sensitive, before, after));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", type),
                Bound("P", type),
                Bound("L", type),
                Bound("S", type),
                Bound("E", type),
                Bound("K", type),
                Bound("Before", type),
                Bound("After", type),
                Bound("p", Arrow(state, publicType)),
                Bound("l", Arrow(state, addedType)),
                Bound("s", Arrow(state, sensitiveType)),
                Bound("e", Arrow(state, targetType)),
                Bound("k", Arrow(state, forcedType)),
                Bound("before", Arrow(state, beforeType)),
                Bound("after", Arrow(state, afterType)),
            ],
            Implies(obstruction, new Formula.Not(simultaneous))));
    }
}
