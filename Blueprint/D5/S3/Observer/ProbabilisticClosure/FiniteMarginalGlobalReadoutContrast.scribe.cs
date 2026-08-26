using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure;

internal sealed class FiniteMarginalGlobalReadoutContrastDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite compatible marginals need not be globally realizable by a readout image.",
        H("Finite Marginal Global Readout Contrast"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("readout-image-is-measurable"),
                Handle("readout_image_measurable"),
                H("The finite-subset readout image is measurable"),
                StatementSource.FromAuthor(
                    Disp(Seq(Call("MeasurableSet", Call("range", F.Id("readout"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite-subset domain is countable, so its readout range is a "
                        + "countable measurable set in the countable-coordinate product."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-marginal-family-probability"),
                Handle("finite_marginal_family_probability"),
                H("Every finite marginal is a probability measure"),
                StatementSource.FromAuthor(ForallJ(
                    Call("IsProbabilityMeasure", Apply(F.Id("finiteMarginal"), F.Id("J"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each finite coordinate law is the finite product of the fair "
                        + "Bernoulli probability measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-marginal-family-compatible"),
                Handle("finite_marginal_family_compatible"),
                H("Finite marginals are the restrictions of the product law"),
                StatementSource.FromAuthor(ForallJ(Disp(Seq(
                    Call("map", Call("restrict", F.Id("J")), F.Id("fairProduct")),
                    Sp, Eq, Sp, Apply(F.Id("finiteMarginal"), F.Id("J")), Dot)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib's infinite product restriction theorem supplies the "
                        + "compatibility equation directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("readout-image-is-null"),
                Handle("readout_image_null"),
                H("The finite-subset image has zero product measure"),
                StatementSource.FromAuthor(Disp(Seq(
                    Apply(F.Id("fairProduct"), Call("range", F.Id("readout"))),
                    Sp, Eq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every readout has finite support, whereas independent activation "
                        + "events occur infinitely often almost surely."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("identity-readout-image-full"),
                Handle("identity_readout_image_full"),
                H("The identity readout is the positive comparison"),
                StatementSource.FromAuthor(Disp(Seq(
                    Apply(F.Id("fairProduct"), Call("range", F.Id("identityReadout"))),
                    Sp, Eq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity readout is surjective onto the full path space, so "
                        + "its image is the whole probability space."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("constant-readout-image-null"),
                Handle("constant_readout_image_null"),
                H("The constant readout has null image in the fair product"),
                StatementSource.FromAuthor(Disp(Seq(
                    Apply(F.Id("fairProduct"), Call("range", F.Id("constantReadout"))),
                    Sp, Eq, Sp, D(0), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A constant readout has singleton, hence finitely supported, image; "
                        + "the product assigns that image zero mass."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("surjective-readout-full-image"),
                Handle("surjective_readout_has_full_image"),
                H("Surjectivity forces full image measure"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Surjective"), Open, F.Id("q"), Close, Sp, Rightarrow, Sp,
                    Apply(F.Id("nu"), Call("range", F.Id("q"))), Sp, Eq, Sp,
                    Apply(F.Id("nu"), F.Id("univ")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the general image audit: no measurability or probability "
                        + "assumption is needed for the set equality itself."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-readout-surjective"),
                Handle("finite_readout_surjective"),
                H("The finite-index readout is surjective"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Surjective"), Open,
                    Apply(F.Id("finiteReadout"), F.Id("J")), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For finite J, filtering the finite universe by a Boolean path "
                        + "constructs a preimage for every path."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-index-readout-image-full"),
                Handle("finite_index_readout_image_full"),
                H("Finite index gives full image for the canonical finite readout"),
                StatementSource.FromAuthor(Disp(Seq(
                    Apply(Apply(F.Id("finiteMarginal"), F.Id("J")),
                        Call("range", Apply(F.Id("finiteReadout"), F.Id("J")))),
                    Sp, Eq, Sp, D(1), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This includes J equal to the empty finset, so zero index is "
                        + "explicitly covered."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-domain-readout-image-empty"),
                Handle("empty_domain_readout_image_empty"),
                H("An empty domain has empty readout image"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("range", F.Id("q")), Sp, Eq, Sp, F.Id("emptyset"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty-domain case cannot be conull for a probability measure."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("singleton-domain-readout-image-singleton"),
                Handle("singleton_domain_readout_image_singleton"),
                H("A one-point domain has singleton image"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("range", F.Id("q")), Sp, Eq, Sp,
                    Call("singleton", Apply(F.Id("q"), F.Id("unit"))), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every map from PUnit is constant, making the singleton image "
                        + "explicit rather than silently assuming surjectivity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fpod-principle-120-1"),
                Handle("fpod_principle_120_1"),
                H("Finite compatibility does not imply global realizability"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The theorem combines probability of every finite marginal, exact "
                        + "restriction compatibility, measurability of the image, the "
                        + "null counterexample, and the conull identity comparison."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create(
        "D5/S3/Observer/ProbabilisticClosure/FiniteMarginalGlobalReadoutContrast." + name);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula ForallJ(Formula body) => Disp(Seq(
        Forall, Sp, F.Id("J"), Colon, Sp, F.Id("FinsetNat"), Comma, Sp, body, Dot));

    private static Formula MainFormula()
    {
        Formula probability = ForallJ(Call(
            "IsProbabilityMeasure", Apply(F.Id("finiteMarginal"), F.Id("J"))));
        Formula compatibility = ForallJ(Disp(Seq(
            Call("map", Call("restrict", F.Id("J")), F.Id("fairProduct")),
            Sp, Eq, Sp, Apply(F.Id("finiteMarginal"), F.Id("J")), Dot)));
        Formula imageMeasurable = Call("MeasurableSet", Call("range", F.Id("readout")));
        Formula imageNull = Seq(
            Apply(F.Id("fairProduct"), Call("range", F.Id("readout"))),
            Sp, Eq, Sp, D(0));
        Formula identityFull = Seq(
            Apply(F.Id("fairProduct"), Call("range", F.Id("identityReadout"))),
            Sp, Eq, Sp, D(1));
        return Disp(Seq(probability, Sp, Land, Sp, compatibility, Sp, Land, Sp,
            imageMeasurable, Sp, Land, Sp, imageNull, Sp, Land, Sp, identityFull, Dot));
    }
}
