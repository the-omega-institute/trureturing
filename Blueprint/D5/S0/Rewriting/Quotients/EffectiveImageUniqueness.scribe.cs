using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting.Quotients;

internal sealed class EffectiveImageUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A descended process map is uniquely determined on the effective image of its "
        + "concept readout, and globally unique when that readout is surjective.",
        H("Effective-Image Uniqueness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("effective-image-uniqueness-of-descended-map"),
                DeclarationHandle.Create(
                    "D5/S0/Rewriting/Quotients/EffectiveImageUniqueness."
                    + "effective_image_uniqueness"),
                H("A descended map is unique exactly where the readout reaches"),
                StatementSource.FromAuthor(EffectiveImageUniquenessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let two maps on the concept-value domain make the same process and "
                            + "future-readout square commute. They agree after composition with "
                            + "the current concept readout, hence agree at every value in its "
                            + "effective image.")),
                    Paragraph(Text(
                        "When the current readout is surjective, agreement on its image is "
                            + "global agreement. When it is not surjective, a candidate makes "
                            + "the square commute exactly when it agrees with the first descended "
                            + "map on every reached value; at least one unreached value remains "
                            + "and its output requires an additional definition.")),
                    Paragraph(Text(
                        "The proof directly applies Mathlib's "
                            + "Function.Surjective.injective_comp_right for global uniqueness "
                            + "and Set.eqOn_range for the exact effective-image restriction. "
                            + "Repository search found the adjacent DynamicsDescent theorem, "
                            + "but it treats surjective self-map descent rather than this general "
                            + "two-readout image statement. This closes atom "
                            + "generic-residual-26cd00f090db8b2a61150a3fef3a8d706caf0c313eb6"
                            + "cb6eae0fbb21bfbed4dc without asserting descent existence."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Commutes(
        Formula future, Formula process, Formula descended, Formula concept) =>
        Seq(
            future, Sp, Circ, Sp, process, Sp, Eq, Sp,
            descended, Sp, Circ, Sp, concept);

    private static Formula ImageAgreement(
        Formula state, Formula concept, Formula left, Formula right)
    {
        Formula x = F.Id("x");
        return Seq(
            Forall, Sp, x, Colon, Sp, state, Comma, Sp,
            Apply(left, Apply(concept, x)), Sp, Eq, Sp,
            Apply(right, Apply(concept, x)));
    }

    private static Formula EffectiveImageUniquenessFormula()
    {
        Formula state = F.Id("X");
        Formula processTarget = F.Id("Y");
        Formula conceptValue = F.Id("BC");
        Formula futureValue = F.Id("BD");
        Formula concept = F.Id("qC");
        Formula future = F.Id("qD");
        Formula process = F.Id("F");
        Formula descended = F.Id("barF");
        Formula other = F.Id("barG");
        Formula candidate = F.Id("H");
        Formula missed = F.Id("b");
        Formula witness = F.Id("x");

        Formula imageAgreement = ImageAgreement(state, concept, descended, other);
        Formula candidateCriterion = Seq(
            Forall, Sp, candidate, Colon, Sp,
            conceptValue, Sp, To, Sp, futureValue, Comma, Sp,
            Open, Commutes(future, process, candidate, concept),
            Sp, Iff, Sp,
            ImageAgreement(state, concept, candidate, descended), Close);
        Formula missedValue = Seq(
            Exists, Sp, missed, Colon, Sp, conceptValue, Comma, Sp,
            Neg, Sp, Exists, Sp, witness, Colon, Sp, state, Comma, Sp,
            Apply(concept, witness), Sp, Eq, Sp, missed);

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, processTarget, Comma, Sp,
            conceptValue, Comma, Sp, futureValue, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak,
            concept, Colon, Sp, state, Sp, To, Sp, conceptValue, Comma, Sp,
            future, Colon, Sp, processTarget, Sp, To, Sp, futureValue, Comma, Sp,
            process, Colon, Sp, state, Sp, To, Sp, processTarget, Comma, RowBreak,
            descended, Comma, Sp, other, Colon, Sp,
            conceptValue, Sp, To, Sp, futureValue, Comma, RowBreak,
            Open, Commutes(future, process, descended, concept), Sp, Land, Sp,
            Commutes(future, process, other, concept), Close, Sp, Rightarrow, RowBreak,
            Open,
            Open, Call("Surjective", concept), Sp, Rightarrow, Sp,
            descended, Sp, Eq, Sp, other, Close, Sp, Land, RowBreak,
            Open, Neg, Sp, Call("Surjective", concept), Sp, Rightarrow, Sp,
            Open, imageAgreement, Sp, Land, RowBreak,
            candidateCriterion, Sp, Land, RowBreak,
            missedValue, Close, Close,
            Close, Dot));
    }
}
