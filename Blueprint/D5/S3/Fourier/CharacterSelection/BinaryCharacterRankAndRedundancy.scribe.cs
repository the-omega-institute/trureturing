using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class BinaryCharacterRankAndRedundancyDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Fourier/CharacterSelection/BinaryCharacterRankAndRedundancy."
            + "binary_character_rank_and_redundancy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary-character span rank counts independent joint outputs and identifies redundant roles.",
        H("Binary Character Rank And Redundancy"),
        Blocks(Describe.Lean(
            DescribeId.Create("binary-character-rank-and-redundancy"),
            DeclarationHandle.Create(Declaration),
            H("Rank counts profiles and span dependence gives product recovery"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Each role is a binary linear character on the canonical quotient of a "
                        + "finite abelian group by doubles. Their joint profile is evaluated "
                        + "back on the original group.")),
                Paragraph(Text(
                    "The realized profile count is two raised to the finite dimension of the "
                        + "character span. A role lying in the span of all other roles has a "
                        + "finite coefficient witness whose multiplicative output is their product."))),
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
        Formula role = F.Id("i");
        Formula selectedRole = F.Id("j");
        Formula element = F.Id("g");
        Formula coefficients = F.Id("a");
        Formula field = Call("ZMod", D(2));
        Formula quotient = Call("ModN", group, D(2));
        Formula dual = Call("Dual", field, quotient);
        Formula quotientPoint = Call("mkQ", D(2), element);
        Formula profile = F.Id("Phi");
        Formula span = F.Id("H");
        Formula rank = F.Id("r");
        Formula otherRoles = Seq(roleIndex, Sp, Setminus, Sp,
            OpenBrace, selectedRole, CloseBrace);
        Formula existingValue = Apply(Apply(characters, role), quotientPoint);
        Formula selectedValue = Apply(Apply(characters, selectedRole), quotientPoint);
        Formula profileDefinition = Seq(
            Apply(profile, element), Sp, Colon, Eq, Sp,
            Grp(existingValue, Underscore,
                Grp(role, Sp, InMacro, Sp, roleIndex)));
        Formula spanDefinition = Seq(
            span, Sp, Colon, Eq, Sp,
            Call("span", field, Call("range", characters)));
        Formula rankDefinition = Seq(
            rank, Sp, Colon, Eq, Sp, Call("finrank", field, span));
        Formula profileCount = Seq(
            Call("card", Call("range", profile)), Sp, Eq, Sp,
            new Formula.Power(D(2), rank));
        Formula restrictedCharacters = Call("restrict", characters, otherRoles);
        Formula spanPremise = Seq(
            Apply(characters, selectedRole), Sp, InMacro, Sp,
            Call("span", field, Call("range", restrictedCharacters)));
        Formula weightedValue = Seq(
            Apply(coefficients, role), Sp, Cdot, Sp, existingValue);
        Formula recoveredProduct = Seq(
            Prod, Underscore,
            Grp(role, Sp, InMacro, Sp, Call("support", coefficients)), Sp,
            Call("ofAdd", weightedValue));
        Formula recovery = Seq(
            Exists, Sp, coefficients, Colon, Sp,
            Call("Finsupp", otherRoles, field), Comma, Sp,
            Forall, Sp, element, Sp, InMacro, Sp, group, Comma, Sp,
            Call("ofAdd", selectedValue), Sp, Eq, Sp, recoveredProduct);
        Formula redundancyClause = Seq(
            Forall, Sp, selectedRole, Sp, InMacro, Sp, roleIndex, Comma, Sp,
            spanPremise, Sp, Rightarrow, Sp, recovery);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, group, Comma, Sp, roleIndex, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            Typeclass("AddCommGroup", group), Comma, Sp,
            Typeclass("Fintype", group), Comma, Sp,
            Typeclass("Fintype", roleIndex), Comma, RowBreak, Grp(),
            characters, Colon, Sp, roleIndex, Sp, To, Sp, dual, Comma,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            profileDefinition, Comma, Sp, spanDefinition, Comma, Sp,
            rankDefinition, Close, SemiSpace, RowBreak, Grp(),
            profileCount, Sp, Land, RowBreak, Grp(),
            redundancyClause, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
