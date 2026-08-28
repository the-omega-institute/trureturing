using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class AllPrimeSplittingProfileNoninjectivityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/Splitting/AllPrimeSplittingProfileNoninjectivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite discriminant splitting readout at every prime does not recover a binary "
            + "quadratic form, although the readout distinguishes some forms.",
        H("All-Prime Splitting Profiles Do Not Recover Global Forms"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("discriminant-splitting-type"),
                Handle("DiscriminantSplittingType"),
                H("Finite discriminant splitting type"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The selected finite interface has three readings: inert, ramified, and "
                        + "split."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("discriminant-splitting-readout"),
                Handle("discriminantSplittingType"),
                H("Discriminant splitting readout"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At an index p, the readout maps the Jacobi symbol of the form's "
                        + "discriminant to inert, ramified, or split according as the value is "
                        + "minus one, zero, or one. It is total and decidable."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("same-all-prime-splitting-profile"),
                Handle("SameAllPrimeSplittingProfile"),
                H("Equality of all-prime splitting profiles"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two forms have the same profile when their finite readouts agree at every "
                        + "natural index carrying a proof of primality."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("all-prime-splitting-profile-is-not-injective"),
                Handle("all_prime_splitting_profile_not_injective"),
                H("The all-prime splitting profile is not injective"),
                StatementSource.FromAuthor(NoninjectivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The forms x squared plus y squared and x squared plus two x y plus "
                            + "two y squared are unequal coefficient triples, but both have "
                            + "discriminant minus four.")),
                    Paragraph(Text(
                        "Equal discriminants give equal Jacobi readouts at every natural index, "
                            + "so in particular the two forms agree at every prime. Primality is "
                            + "only the interface label in this collision.")),
                    Paragraph(Text(
                        "This deliberately proves only that the finite splitting interface is "
                            + "too coarse. It makes no claim of local equivalence over any ring "
                            + "of p-adic integers and uses no genus theory."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("splitting-profile-distinguishes-some-global-forms"),
                Handle("splitting_profile_distinguishes_some_global_forms"),
                H("The splitting profile distinguishes some global forms"),
                StatementSource.FromAuthor(DistinguishingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The discriminant-one control form and the zero form are unequal and have "
                        + "different readings at the prime three. Thus the selected interface "
                        + "is coarse but not constant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reference-form-realizes-all-splitting-types"),
                Handle("reference_form_realizes_all_splitting_types"),
                H("One reference form realizes all three readings"),
                StatementSource.FromAuthor(AllTypesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The nonzero form x squared plus y squared is inert at three, ramified at "
                        + "two, and split at five under the selected discriminant readout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-form-is-ramified-above-one"),
                Handle("zero_form_is_ramified_above_one"),
                H("The zero form ramifies above index one"),
                StatementSource.FromAuthor(ZeroFormAboveOneFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The zero form has discriminant zero. At every index p strictly above one, "
                        + "the Jacobi symbol of zero is zero, so the finite readout is ramified. "
                        + "This weakens primality to the exact condition used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("index-above-one-is-necessary-for-zero-form-ramification"),
                Handle("index_above_one_is_necessary_for_zero_form_ramification"),
                H("The lower index bound is necessary for zero-form ramification"),
                StatementSource.FromAuthor(IndexBoundNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the totalized nonprime indices zero and one, the zero form reads split "
                        + "rather than ramified. These concrete cases witness that the strict "
                        + "lower bound in the preceding theorem cannot be dropped."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(Prefix + name);

    private static Formula Profile(Formula form, Formula index) =>
        Call("discriminantSplittingType", form, index);

    private static Formula NoninjectivityFormula()
    {
        Formula first = F.Id("collisionFormOne");
        Formula second = F.Id("collisionFormTwo");
        Formula index = F.Id("p");

        return Disp(Seq(
            Call("Neq", first, second), Sp, Land, RowBreak,
            Forall, Sp, index, Colon, Sp, F.Id("Nat"), Comma, Sp,
            Call("Prime", index), Sp, Rightarrow, Sp,
            Profile(first, index), Sp, Eq, Sp, Profile(second, index), Dot));
    }

    private static Formula DistinguishingFormula()
    {
        Formula first = F.Id("splitControlForm");
        Formula second = F.Id("zeroForm");
        Formula index = F.Id("p");

        return Disp(Seq(
            Call("Neq", first, second), Sp, Land, RowBreak,
            Exists, Sp, index, Colon, Sp, F.Id("Nat"), Comma, Sp,
            Call("Prime", index), Sp, Land, Sp,
            Call("Neq", Profile(first, index), Profile(second, index)), Dot));
    }

    private static Formula AllTypesFormula()
    {
        Formula form = F.Id("collisionFormOne");

        return Disp(Seq(
            Profile(form, D(3)), Sp, Eq, Sp, F.Id("inert"), Sp, Land, RowBreak,
            Profile(form, D(2)), Sp, Eq, Sp, F.Id("ramified"), Sp, Land, RowBreak,
            Profile(form, D(5)), Sp, Eq, Sp, F.Id("split"), Dot));
    }

    private static Formula ZeroFormAboveOneFormula()
    {
        Formula index = F.Id("p");

        return Disp(Seq(
            Forall, Sp, index, Colon, Sp, F.Id("Nat"), Comma, Sp,
            D(1), Sp, Lt, Sp, index, Sp, Rightarrow, Sp,
            Profile(F.Id("zeroForm"), index), Sp, Eq, Sp, F.Id("ramified"), Dot));
    }

    private static Formula IndexBoundNecessaryFormula() => Disp(Seq(
        Profile(F.Id("zeroForm"), D(0)), Sp, Eq, Sp, F.Id("split"), Sp, Land,
        RowBreak, Profile(F.Id("zeroForm"), D(1)), Sp, Eq, Sp, F.Id("split"), Dot));
}
