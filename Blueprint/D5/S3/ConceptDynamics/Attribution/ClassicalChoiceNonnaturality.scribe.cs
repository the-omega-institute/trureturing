using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ClassicalChoiceNonnaturalityDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Attribution/ClassicalChoiceNonnaturality."
            + "classical_choice_family_is_nonnatural";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classical choice supplies finite selectors, but the resulting family is not natural.",
        H("Classical-Choice Nonnaturality"),
        Blocks(Describe.Lean(
            DescribeId.Create("classical-choice-family-is-nonnatural"),
            DeclarationHandle.Create(Declaration),
            H("The classical-choice family is not natural"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For each finite nonempty carrier, the displayed family selects the element "
                    + "supplied by the choice axiom. If this same family commuted with every "
                    + "bijection, it would contradict the canonical two-point swap "
                    + "obstruction."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula carrier = F.Id("alpha");
        Formula target = F.Id("beta");
        Formula choice = F.Id("choice");
        Formula finiteWitness = F.Id("f");
        Formula nonemptyWitness = F.Id("h");
        Formula finiteCarrier = F.Id("fAlpha");
        Formula finiteTarget = F.Id("fBeta");
        Formula nonemptyCarrier = F.Id("hAlpha");
        Formula nonemptyTarget = F.Id("hBeta");
        Formula bijection = F.Id("e");

        Formula choiceType = Seq(
            Forall, Sp, carrier, Colon, Sp, type, Comma, Sp,
            finiteWitness, Colon, Sp, Call("Fintype", carrier), Comma, Sp,
            nonemptyWitness, Colon, Sp, Call("Nonempty", carrier), Comma, Sp,
            carrier);
        Formula choiceValue = Seq(
            Open, carrier, Comma, Sp, finiteWitness, Comma, Sp,
            nonemptyWitness, Close, Sp, Mapsto, Sp,
            Call("ClassicalChoice", nonemptyWitness));
        Formula naturality = Seq(
            Forall, Sp, carrier, Comma, Sp, target, Colon, Sp, type, Comma, Sp,
            finiteCarrier, Colon, Sp, Call("Fintype", carrier), Comma, Sp,
            finiteTarget, Colon, Sp, Call("Fintype", target), Comma, Sp,
            nonemptyCarrier, Colon, Sp, Call("Nonempty", carrier), Comma, Sp,
            nonemptyTarget, Colon, Sp, Call("Nonempty", target), Comma, Sp,
            bijection, Colon, Sp, Call("Equiv", carrier, target), Comma, Sp,
            EqualTo(
                Apply(
                    bijection,
                    Apply(choice, carrier, finiteCarrier, nonemptyCarrier)),
                Apply(choice, target, finiteTarget, nonemptyTarget)));

        return Disp(new Formula.Aligned([
            Seq(
                Operatorname, Grp(F.Id("let")), Sp, choice, Colon, Sp,
                choiceType, Sp, Colon, Eq, Sp, choiceValue, Comma),
            Seq(Neg, Sp, naturality, Dot),
        ]));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
