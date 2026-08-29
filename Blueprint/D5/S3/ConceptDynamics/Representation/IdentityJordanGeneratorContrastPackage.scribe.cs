using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Representation;

internal sealed class IdentityJordanGeneratorContrastPackageDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Representation/IdentityJordanGeneratorContrastPackage."
            + "identity_jordan_generator_contrast_package";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two minimal polynomials, nonconjugacy, and both characteristic-polynomial "
            + "equalities are exposed by one declaration.",
        H("Identity-Jordan Generator Contrast Package"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("identity-jordan-generator-contrast-package"),
                DeclarationHandle.Create(Declaration),
                H("The full identity-Jordan contrast is packaged together"),
                StatementSource.FromAuthor(PackageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The declaration conjoins the imported minimal-polynomial equalities, "
                            + "the generator nonconjugacy result, and the two imported "
                            + "characteristic-polynomial equalities. Pinned Mathlib has "
                            + "semisimplicity predicates and Jordan-Chevalley decomposition, "
                            + "but no operation constructing a representation's "
                            + "semisimplification. In this fixed rational two-dimensional "
                            + "example, the split characteristic polynomial records two "
                            + "copies of eigenvalue one. The package does not construct "
                            + "semisimplified representations, assert an isomorphism between "
                            + "them, or claim that characteristic-polynomial equality detects "
                            + "semisimplification in general."))),
                DescribeRole.Theorem))));

    private static Formula PackageFormula()
    {
        Formula generator = F.Id("cycleGenerator");
        Formula zeroAction = Call("act", F.Id("rhoZero"), generator);
        Formula unipotentAction = Call("act", F.Id("rhoUnipotent"), generator);
        Formula linearFactor = Seq(F.Id("X"), Sp, Minus, Sp, D(1));
        Formula square = Seq(Open, linearFactor, Close, Caret, D(2));

        Formula zeroMinpoly = Equal(Call("minpolyQ", zeroAction), linearFactor);
        Formula unipotentMinpoly = Equal(Call("minpolyQ", unipotentAction), square);
        Formula notConjugate = Seq(
            Neg, Sp, Call("IsConj", zeroAction, unipotentAction));
        Formula zeroCharpoly = Equal(Call("charpoly", zeroAction), square);
        Formula unipotentCharpoly = Equal(Call("charpoly", unipotentAction), square);

        return Disp(Seq(
            zeroMinpoly, Sp, Land, Sp,
            unipotentMinpoly, Sp, Land, Sp,
            notConjugate, Sp, Land, Sp,
            Open,
            zeroCharpoly, Sp, Land, Sp, unipotentCharpoly,
            Close));
    }
}
