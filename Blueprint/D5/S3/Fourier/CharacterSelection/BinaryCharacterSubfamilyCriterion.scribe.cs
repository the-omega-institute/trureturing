using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class BinaryCharacterSubfamilyCriterionDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Fourier/CharacterSelection/BinaryCharacterSubfamilyCriterion."
            + "binary_character_subfamily_sufficiency_tfae";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A binary-character subfamily is sufficient exactly when it spans the full role space.",
        H("Binary Character Subfamily Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("binary-character-subfamily-criterion"),
                DeclarationHandle.Create(Declaration),
                H("Observation kernels, expressible targets, and character spans agree"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be a set of binary characters on a finite abelian group and "
                            + "let B be a subset. Each character is evaluated on the original "
                            + "group through the canonical quotient by doubles.")),
                    Paragraph(Text(
                        "The displayed profile is the canonical joint readout of a character "
                            + "set. Expressibility uses its canonical effective-image readout "
                            + "and the repository refinement relation.")),
                    Paragraph(Text(
                        "The public three-way equivalence states equality of observation "
                            + "kernels, equality of expressible target families for every "
                            + "target type, and equality of binary-character spans."))),
                DescribeRole.Theorem))));

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

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula group = F.Id("G");
        Formula allRoles = F.Id("E");
        Formula chosenRoles = F.Id("B");
        Formula roleSet = F.Id("S");
        Formula element = F.Id("g");
        Formula character = F.Id("chi");
        Formula targetType = F.Id("Y");
        Formula target = F.Id("K");
        Formula field = Call("ZMod", D(2));
        Formula quotient = Call("ModN", group, D(2));
        Formula dual = Call("Dual", field, quotient);
        Formula roleSetType = Call("Set", dual);
        Formula profile = F.Id("profile");
        Formula Profile(Formula roles) => Apply(profile, roles);
        Formula quotientPoint = Call("mkQ", D(2), element);
        Formula profileDefinition = Seq(
            Apply(Apply(Profile(roleSet), element), character), Sp, Colon, Eq, Sp,
            Apply(character, quotientPoint));
        Formula fullSpan = F.Id("H");
        Formula fullSpanDefinition = Seq(
            fullSpan, Sp, Colon, Eq, Sp, Call("span", field, allRoles));
        Formula kernelClause = Seq(
            Call("ker", Profile(chosenRoles)), Sp, Eq, Sp,
            Call("ker", Profile(allRoles)));
        Formula TargetFamily(Formula roles) => Seq(
            OpenBrace, target, Colon, Sp, group, Sp, To, Sp, targetType,
            Sp, Mid, Sp,
            Call("Refines", target,
                Call("effectiveReadout", Profile(roles))), CloseBrace);
        Formula targetsClause = Seq(
            Forall, Sp, targetType, Colon, Sp,
            Operatorname, Grp(F.Id("Type")), Comma, Sp,
            TargetFamily(chosenRoles), Sp, Eq, Sp, TargetFamily(allRoles));
        Formula spanClause = Seq(
            Call("span", field, chosenRoles), Sp, Eq, Sp, fullSpan);
        Formula clauses = Grp(
            OpenBracket,
            kernelClause, Comma, Sp,
            targetsClause, Comma, Sp,
            spanClause,
            CloseBracket);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, group, Comma, Sp,
            allRoles, Comma, Sp, chosenRoles, Comma, RowBreak, Grp(),
            Typeclass("AddCommGroup", group), Comma, Sp,
            Typeclass("Finite", group), Comma, RowBreak, Grp(),
            allRoles, Comma, Sp, chosenRoles, Colon, Sp, roleSetType, Comma,
            RowBreak, Grp(),
            chosenRoles, Sp, Subseteq, Sp, allRoles, Sp, Rightarrow,
            RowBreak, Grp(),
            Operatorname, Grp(F.Id("let")), Open,
            profileDefinition, Comma, Sp,
            fullSpanDefinition, Close, SemiSpace, RowBreak, Grp(),
            Call("ListTFAE", clauses), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
