using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class NoNaturalFiniteChoiceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No selector on every nonempty finite carrier is invariant under all bijections.",
        H("No Natural Finite Choice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("no-natural-finite-choice"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Attribution/NoNaturalFiniteChoice."
                        + "no_natural_finite_choice"),
                H("No natural finite choice"),
                StatementSource.FromAuthor(NoChoiceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A selector is supplied for every finite nonempty carrier, and its "
                            + "value is required to transport along every bijection between "
                            + "carriers. On the two-point carrier, swapping the two elements "
                            + "would have to fix the selected element.")),
                    Paragraph(Text(
                        "The swap has no fixed point, so the transport law is impossible. "
                            + "The carrier type, finiteness and nonemptiness witnesses, and "
                            + "the bijection are all explicit in the statement."))),
                DescribeRole.Theorem))));

    private static Formula NoChoiceFormula()
    {
        Formula type = F.Id("Type");
        Formula carrier = F.Id("alpha");
        Formula target = F.Id("beta");
        Formula element = F.Id("choice");
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
                    Apply(element, carrier, finiteCarrier, nonemptyCarrier)),
                Apply(element, target, finiteTarget, nonemptyTarget)));

        return Disp(Seq(
            Neg, Sp, Exists, Sp, element, Colon, Sp, choiceType, Comma, Sp,
            naturality, Dot));
    }

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
