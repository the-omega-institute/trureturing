using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class BinaryCharacterRedundancyCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary character is redundant exactly when it lies in the existing span.",
        H("Binary Character Redundancy Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-character-redundancy-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/BinaryCharacterRedundancyCriterion."
                        + "binary_character_redundancy_criterion"),
                H("Kernel preservation, span membership, and output recovery are equivalent"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let G be an abelian group and let I be a finite role-index type. "
                            + "Every binary character is a linear functional on the canonical "
                            + "quotient of G by doubles, evaluated on G through the quotient map.")),
                    Paragraph(Text(
                        "The first public clause says that the new character vanishes whenever "
                            + "all existing characters vanish. The second says directly that it "
                            + "belongs to the binary-field span of the existing character range.")),
                    Paragraph(Text(
                        "The third clause exposes finite coefficients. At every group element, "
                            + "the multiplicative output of the new character is recovered as "
                            + "the finite product of the corresponding weighted existing outputs.")),
                    Paragraph(Text(
                        "The proof applies the pinned library kernel-span criterion and finite-span "
                            + "coefficient theorem, then uses ofAdd_sum for the product formula."))),
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

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula roleIndex = F.Id("I");
        Formula characters = F.Id("chi");
        Formula newCharacter = F.Id("eta");
        Formula coefficients = F.Id("a");
        Formula element = F.Id("g");
        Formula index = F.Id("i");
        Formula field = Call("ZMod", D(2));
        Formula quotient = Call("ModN", group, D(2));
        Formula dual = Call("Dual", field, quotient);
        Formula quotientPoint = Call("mkQ", D(2), element);
        Formula existingValue = Apply(Apply(characters, index), quotientPoint);
        Formula newValue = Apply(newCharacter, quotientPoint);
        Formula jointKernel = Seq(
            Forall, Sp, index, Sp, InMacro, Sp, roleIndex, Comma, Sp,
            existingValue, Sp, Eq, Sp, D(0));
        Formula kernelClause = Seq(
            Forall, Sp, element, Sp, InMacro, Sp, group, Comma, Sp,
            Open, jointKernel, Close, Sp, Rightarrow, Sp,
            newValue, Sp, Eq, Sp, D(0));
        Formula spanClause = Seq(
            newCharacter, Sp, InMacro, Sp,
            Call("span", field, Call("range", characters)));
        Formula weightedValue = Seq(
            Apply(coefficients, index), Sp, Cdot, Sp, existingValue);
        Formula recoveredProduct = Seq(
            Prod, Underscore,
            Grp(index, Sp, InMacro, Sp, Call("support", coefficients)), Sp,
            Call("ofAdd", weightedValue));
        Formula recoveryClause = Seq(
            Exists, Sp, coefficients, Colon, Sp,
            Call("Finsupp", roleIndex, field), Comma, Sp,
            Forall, Sp, element, Sp, InMacro, Sp, group, Comma, Sp,
            Call("ofAdd", newValue), Sp, Eq, Sp, recoveredProduct);
        Formula clauses = Grp(
            OpenBracket,
            kernelClause, Comma, Sp,
            spanClause, Comma, Sp,
            recoveryClause,
            CloseBracket);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, group, Comma, Sp, roleIndex, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            Typeclass("AddCommGroup", group), Comma, Sp,
            Typeclass("Finite", roleIndex), Comma, RowBreak, Grp(),
            characters, Colon, Sp, roleIndex, Sp, To, Sp, dual, Comma,
            RowBreak, Grp(),
            newCharacter, Colon, Sp, dual, Comma, RowBreak, Grp(),
            Call("ListTFAE", clauses), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
