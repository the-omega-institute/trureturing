using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class QuarticCharacterCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/Splitting/QuarticCharacterCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quartic modulo-five character completes the mod-sixty splitting profile.",
        H("Quartic Character Completion Modulo Sixty"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chi-minus-four"),
                DeclarationHandle.Create(Prefix + "chiMinusFour"),
                H("The Gaussian quadratic character"),
                StatementSource.FromAuthor(CharacterFormula(ChiMinusFour(), D(2))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Gaussian split-inert reading is composed with the standard "
                        + "binary root character to obtain a homomorphism into mu two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chi-minus-three"),
                DeclarationHandle.Create(Prefix + "chiMinusThree"),
                H("The Eisenstein quadratic character"),
                StatementSource.FromAuthor(CharacterFormula(ChiMinusThree(), D(2))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Eisenstein split-inert reading is composed with the same standard "
                        + "binary root character."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("psi-five"),
                DeclarationHandle.Create(Prefix + "psiFive"),
                H("The quartic modulo-five character"),
                StatementSource.FromAuthor(CharacterFormula(PsiFive(), D(4))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Reduction from units modulo sixty to units modulo five is followed "
                            + "by the discrete logarithm base two and the standard character "
                            + "into the fourth roots of unity.")),
                    Paragraph(Text(
                        "The discrete logarithm table is total on the four unit residues. "
                            + "Its identity and multiplication laws are checked on that "
                            + "finite group, so the definition is representative-independent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("psi-sixty"),
                DeclarationHandle.Create(Prefix + "psiSixty"),
                H("The quadratic-quadratic-quartic completion"),
                StatementSource.FromAuthor(CompletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The completed map records the Gaussian and Eisenstein quadratic "
                        + "characters together with the quartic modulo-five character."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mod-five-generator-maps-to-i"),
                DeclarationHandle.Create(
                    Prefix + "psi_five_maps_mod_five_generator_two_to_i"),
                H("The modulo-five generator maps to i"),
                StatementSource.FromAuthor(GeneratorFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The unit class seven reduces to the generator two modulo five. Its "
                        + "discrete logarithm is one, so the standard quartic character "
                        + "takes the value i."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("quartic-completion-is-injective"),
                DeclarationHandle.Create(Prefix + "psi_sixty_injective"),
                H("The quartic completion separates every unit class"),
                StatementSource.FromAuthor(InjectivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equality of completed values recovers the Gaussian and Eisenstein "
                            + "readings and the full modulo-five residue.")),
                    Paragraph(Text(
                        "These data give equal three-ring profiles and equal orientation "
                            + "bits. The preceding orientation theorem then forces the two "
                            + "unit classes to be equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("binary-collision-quartic-separation"),
                DeclarationHandle.Create(
                    Prefix
                        + "quadratic_profile_collision_but_quartic_completion_separates"),
                H("The quartic coordinate strictly improves the binary profile"),
                StatementSource.FromAuthor(ContrastFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The distinct classes one and forty-nine have the same three-ring "
                        + "binary profile, while the completed character values differ. "
                        + "This is the concrete mu-two-cubed versus mu-two-squared times "
                        + "mu-four contrast."))),
                DescribeRole.Theorem))));

    private static Formula Call(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Mu(Formula index) =>
        new Formula.Subscript(F.Id("mu"), index);

    private static Formula ChiMinusFour() =>
        new Formula.Subscript(F.Id("chi"), Seq(Minus, D(4)));

    private static Formula ChiMinusThree() =>
        new Formula.Subscript(F.Id("chi"), Seq(Minus, D(3)));

    private static Formula PsiFive() =>
        new Formula.Subscript(F.Id("psi"), D(5));

    private static Formula PsiSixty() =>
        new Formula.Subscript(F.Id("Psi"), D(6, 0));

    private static Formula UnitsModSixty() => Seq(
        Open, Mathbb, Grp(F.Id("Z")), Slash, D(6, 0),
        Mathbb, Grp(F.Id("Z")), Close, Caret, Grp(Times));

    private static Formula CharacterFormula(Formula character, Formula order) =>
        Disp(Seq(
            character, Colon, Sp, UnitsModSixty(), Sp, To, Sp, Mu(order), Dot));

    private static Formula CompletionFormula() => Disp(Seq(
        PsiSixty(), Sp, Eq, Sp,
        Open, ChiMinusFour(), Comma, Sp, ChiMinusThree(), Comma, Sp, PsiFive(), Close,
        Colon, Sp, UnitsModSixty(), Sp, To, Sp,
        Mu(D(2)), Sp, Times, Sp, Mu(D(2)), Sp, Times, Sp, Mu(D(4)), Dot));

    private static Formula GeneratorFormula() => Disp(Seq(
        Call(PsiFive(), D(7)), Sp, Eq, Sp, F.Id("i"), Dot));

    private static Formula InjectivityFormula()
    {
        Formula left = F.Id("u");
        Formula right = F.Id("v");
        return Disp(Seq(
            Forall, Sp, left, Comma, Sp, right, Colon, Sp, UnitsModSixty(), Comma, Sp,
            Call(PsiSixty(), left), Sp, Eq, Sp, Call(PsiSixty(), right), Sp,
            Rightarrow, Sp, left, Sp, Eq, Sp, right, Dot));
    }

    private static Formula ContrastFormula()
    {
        Formula left = F.Id("u");
        Formula right = F.Id("v");
        Formula image = F.Id("triRingImage");
        return Disp(Seq(
            Exists, Sp, left, Comma, Sp, right, Colon, Sp, UnitsModSixty(), Comma, Sp,
            left, Sp, Neq, Sp, right, Sp, Land, RowBreak, Grp(),
            Call(image, left), Sp, Eq, Sp, Call(image, right), Sp, Land, RowBreak, Grp(),
            Call(PsiSixty(), left), Sp, Neq, Sp, Call(PsiSixty(), right), Dot));
    }
}
