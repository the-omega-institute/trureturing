using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Splitting;

internal sealed class HilbertReciprocityParityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/Splitting/HilbertReciprocityParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite sign code recovers one coordinate and exposes omitted load-bearing places.",
        H("Hilbert Reciprocity as a Global Sign-Parity Check"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hilbert-reciprocity-code"),
                Handle("hilbertReciprocityCode"),
                H("Hilbert reciprocity code"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A codeword is a sign profile with a finite carrier, value one away "
                            + "from that carrier, and product one on the carrier.")),
                    Paragraph(Text(
                        "Hilbert symbols form one arithmetic instance of this abstraction. "
                            + "This module does not define or construct a Hilbert symbol."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-sign-equals-product-of-other-places"),
                Handle("local_sign_eq_product_of_other_places"),
                H("One local sign is determined by all the others"),
                StatementSource.FromAuthor(LocalRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The product-one equation is the explicit hReciprocity premise. For "
                            + "actual Hilbert symbols it comes from the external classical "
                            + "product formula and is not proved or anchored here.")),
                    Paragraph(Text(
                        "Factoring out the chosen coordinate and using that every integer "
                            + "unit is its own inverse gives the product over the remaining "
                            + "finite carrier. A coordinate outside the carrier is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("omitted-place-can-break-reciprocity-check"),
                Handle("omitted_place_can_break_reciprocity_check"),
                H("Omitting a load-bearing place can break the check"),
                StatementSource.FromAuthor(OmissionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On two coordinates, assigning minus one at both gives total product one. "
                        + "Deleting either coordinate leaves product minus one. The abstract "
                        + "coordinates model omitted dyadic or infinite places without "
                        + "constructing arithmetic Hilbert symbols."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reciprocity-code-degeneracy-audit"),
                Handle("reciprocity_code_degeneracy_audit"),
                H("Degenerate carriers and profiles are explicit"),
                StatementSource.FromAuthor(DegeneracyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty profile and every all-one profile pass. On a singleton index "
                        + "type, every codeword is forced to have its sole coordinate equal "
                        + "to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reciprocity-product-is-necessary"),
                Handle("reciprocity_product_is_necessary"),
                H("The reciprocity product premise is necessary"),
                StatementSource.FromAuthor(ProductNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A one-coordinate profile with value minus one has finite support but "
                        + "fails both the product-one premise and local recovery."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-support-coverage-is-necessary"),
                Handle("finite_support_coverage_is_necessary"),
                H("The finite carrier must cover every nontrivial sign"),
                StatementSource.FromAuthor(SupportNecessityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A claimed carrier containing only a positive coordinate has product one, "
                        + "but a negative coordinate outside it violates local recovery. Thus "
                        + "the off-carrier identity condition is necessary."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create(Prefix + name);

    private static Formula LocalRecoveryFormula()
    {
        Formula carrier = F.Id("I");
        Formula places = F.Id("S");
        Formula profile = F.Id("s");
        Formula place = F.Id("v");
        Formula chosen = F.Id("v0");
        Formula signs = F.Id("ZUnits");

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, carrier, Comma, Sp, places, Colon, Sp,
                Call("Finset", carrier), Comma, Sp, profile, Colon, Sp,
                carrier, Sp, To, Sp, signs, Comma, Sp, chosen, Colon, Sp, carrier, Comma,
                Sp, OpenBracket, Call("DecidableEq", carrier), CloseBracket, Comma),
            Seq(Open, Forall, Sp, place, Comma, Sp, Neg,
                Open, place, Sp, InMacro, Sp, places, Close, Sp, Rightarrow, Sp,
                Apply(profile, place), Sp, Eq, Sp, D(1), Close, Sp, Land, Sp),
            Seq(Product(places, place, Apply(profile, place)), Sp, Eq, Sp, D(1),
                Sp, Rightarrow, Sp),
            Seq(Apply(profile, chosen), Sp, Eq, Sp,
                Product(Call("erase", places, chosen), place, Apply(profile, place)), Dot),
        ]));
    }

    private static Formula OmissionFormula()
    {
        Formula profile = F.Id("s");
        Formula place = F.Id("v");
        Formula omitted = F.Id("w");
        Formula universe = Call("univ", F.Id("Fin2"));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, place, Colon, Sp, F.Id("Fin2"), Comma, Sp,
                Apply(profile, place), Sp, Eq, Sp, Minus, D(1), Comma),
            Seq(Call("InCode", profile), Sp, Land, Sp,
                Product(universe, place, Apply(profile, place)), Sp, Eq, Sp, D(1),
                Sp, Land, Sp),
            Seq(Forall, Sp, omitted, Colon, Sp, F.Id("Fin2"), Comma, Sp,
                Product(Call("erase", universe, omitted), place, Apply(profile, place)),
                Sp, Eq, Sp, Minus, D(1), Dot),
        ]));
    }

    private static Formula DegeneracyFormula() => Disp(new Formula.Aligned([
        Seq(Call("InCode", F.Id("emptyProfile")), Sp, Land, Sp),
        Seq(Forall, Sp, F.Id("s"), Colon, Sp, Call("Profile", F.Id("Unit")), Comma, Sp,
            Call("InCode", F.Id("s")), Sp, Rightarrow, Sp,
            Apply(F.Id("s"), F.Id("unit")), Sp, Eq, Sp, D(1), Sp, Land, Sp),
        Seq(Forall, Sp, F.Id("I"), Comma, Sp,
            Call("InCode", Call("allOneProfile", F.Id("I"))), Dot),
    ]));

    private static Formula ProductNecessityFormula()
    {
        Formula profile = F.Id("s");
        Formula place = F.Id("v");
        Formula universe = Call("univ", F.Id("Fin1"));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, place, Colon, Sp, F.Id("Fin1"), Comma, Sp,
                Apply(profile, place), Sp, Eq, Sp, Minus, D(1), Comma),
            Seq(Product(universe, place, Apply(profile, place)), Sp, Neq, Sp, D(1),
                Sp, Land, Sp),
            Seq(Apply(profile, D(0)), Sp, Neq, Sp,
                Product(Call("erase", universe, D(0)), place, Apply(profile, place)), Dot),
        ]));
    }

    private static Formula SupportNecessityFormula()
    {
        Formula profile = F.Id("s");
        Formula place = F.Id("v");
        Formula places = Call("singleton", D(0));
        return Disp(new Formula.Aligned([
            Seq(Apply(profile, D(0)), Sp, Eq, Sp, D(1), Comma, Sp,
                Apply(profile, D(1)), Sp, Eq, Sp, Minus, D(1), Comma),
            Seq(Product(places, place, Apply(profile, place)), Sp, Eq, Sp, D(1),
                Sp, Land, Sp),
            Seq(Neg, Open, Forall, Sp, place, Comma, Sp,
                Neg, Open, place, Sp, InMacro, Sp, places, Close, Sp, Rightarrow, Sp,
                Apply(profile, place), Sp, Eq, Sp, D(1), Close, Sp, Land, Sp),
            Seq(Apply(profile, D(1)), Sp, Neq, Sp,
                Product(Call("erase", places, D(1)), place, Apply(profile, place)), Dot),
        ]));
    }

    private static Formula Product(Formula places, Formula index, Formula value) =>
        Seq(Prod, Underscore, Grp(index, Sp, InMacro, Sp, places), Sp, value);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
