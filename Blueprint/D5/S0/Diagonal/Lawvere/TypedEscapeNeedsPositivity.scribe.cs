using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Lawvere;

internal sealed class TypedEscapeNeedsPositivityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lawvere escape alone does not place the escaped diagonal in the effect interval.",
        H("Typed Escape Needs Positivity"),
        Blocks(
            Paragraph(Text(
                "Diagonal non-capture and effecthood are different requirements. Ordinary "
                    + "complement preserves the effect interval in an ordered additive group, "
                    + "but a fixed-point-free twist on a larger codomain can escape while "
                    + "leaving that interval.")),
            Describe.Lean(
                DescribeId.Create("ordinary-complement-preserves-effects"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity.complement_isEffect"),
                H("Ordinary complement preserves effects"),
                StatementSource.FromAuthor(ComplementPreservesEffectsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E lie between zero and the distinguished order unit in an additive "
                            + "commutative group with a compatible partial order. The upper bound "
                            + "E <= 1 gives 0 <= 1 - E, while the lower bound 0 <= E gives "
                            + "1 - E <= 1. Thus complement carries every effect back into the "
                            + "same order interval."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("lawvere-escape-does-not-imply-the-effect-audit"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Lawvere/TypedEscapeNeedsPositivity."
                        + "typed_escape_does_not_imply_effect_audit"),
                H("Lawvere escape does not imply the effect audit"),
                StatementSource.FromAuthor(TypedEscapeCounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the integers, the complement c(E) = 1 - E has no fixed point: a "
                            + "fixed point would make the odd integer one equal to twice an "
                            + "integer. Take the one-address listing whose sole entry is 2. Its "
                            + "twisted diagonal is -1, so the fixed-point-free Lawvere argument "
                            + "places that diagonal outside the listing's range.")),
                    Paragraph(Text(
                        "The same value -1 is below zero and therefore is not an effect. The "
                            + "listing escapes, but it fails the audit requiring every diagonal "
                            + "value to lie between zero and one. Positivity is consequently an "
                            + "additional typed condition, not a consequence of escape alone."))),
                DescribeRole.Theorem))));

    private static Formula ComplementPreservesEffectsFormula()
    {
        Formula carrier = Id("R");
        Formula effect = Id("E");
        Formula assumptions = new Formula.Logic(
            Call("AddCommGroup", carrier),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Call("PartialOrder", carrier),
                FormulaLogicOperator.And,
                new Formula.Logic(
                    Call("IsOrderedAddMonoid", carrier),
                    FormulaLogicOperator.And,
                    Call("One", carrier))));
        Formula preservation = new Formula.Logic(
            Call("IsEffect", effect),
            FormulaLogicOperator.Implies,
            Call("IsEffect", Subtract(Num(1), effect)));

        return FormulaDsl.Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("R"),
            Id("Type"),
            new Formula.Logic(
                assumptions,
                FormulaLogicOperator.Implies,
                new Formula.Bind(
                    FormulaQuantifier.ForAll,
                    FormulaIdentifier.Create("E"),
                    carrier,
                    preservation))));
    }

    private static Formula TypedEscapeCounterexampleFormula()
    {
        Formula integers = new Formula.Integers();
        Formula complement = Id("c");
        Formula effect = Id("E");
        Formula listing = Id("listing");
        Formula complementAtEffect = new Formula.Apply(complement, [effect]);
        Formula complementDefinition = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("E"),
            integers,
            Equal(complementAtEffect, Subtract(Num(1), effect)));
        Formula fixedPointFree = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("E"),
            integers,
            NotEqual(complementAtEffect, effect));
        Formula escapedWithoutAudit = new Formula.Logic(
            Call("IsEscaped", complement, listing),
            FormulaLogicOperator.And,
            new Formula.Not(Call("PassesEffectAudit", complement, listing)));
        Formula witnessProperties = new Formula.Logic(
            fixedPointFree,
            FormulaLogicOperator.And,
            escapedWithoutAudit);
        Formula listingType = new Formula.TypeArrow(
            Id("Unit"),
            new Formula.TypeArrow(Id("Unit"), integers));
        Formula witness = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("listing"),
            listingType,
            witnessProperties);

        return FormulaDsl.Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("c"),
            new Formula.TypeArrow(integers, integers),
            new Formula.Logic(
                complementDefinition,
                FormulaLogicOperator.Implies,
                witness)));
    }
}
