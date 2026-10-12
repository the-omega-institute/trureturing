using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class CFMPNormalizerCentralizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalizer quotient acts as the full centralizer of the right-coset action.",
        H("Normalizer Quotient and Right-Coset Centralizer"),
        Blocks(Describe.Lean(
            DescribeId.Create("cfmp-normalizer-centralizer"),
            DeclarationHandle.Create(
                "D5/S3/FiniteGroups/CFMPNormalizerCentralizer.normalizerCentralizerIso"),
            H("The generic right-coset centralizer theorem"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an arbitrary group G and subgroup H, Omega_R is the quotient by "
                    + "QuotientGroup.rightRel H and R_a sends H g to H g a. The quotient "
                    + "group is formed inside the normalizer N_G(H), with normality of H "
                    + "there derived from the normalizer definition.")),
                Paragraph(Text(
                    "The isomorphism sends n H to F_n, where F_n(H g) = H n g. "
                    + "Standard function composition gives F_n composed with F_m = F_(n m). "
                    + "An equivariant permutation is determined by its value at H; exact "
                    + "stabilizer preservation forces that value to be H n with n in the "
                    + "normalizer. An element of H acts trivially on every right coset; "
                    + "conversely, evaluating a kernel element at H proves that it lies in H. "
                    + "Thus H.subgroupOf(N_G(H)) equals the kernel of normalizerMap. "
                    + "QuotientGroup.liftEquiv applies directly to this kernel equality "
                    + "and the surjectivity of normalizerMap to give the isomorphism.")),
                Paragraph(Text(
                    "The theorem is the generic algebraic consumer for CFMP source clauses "
                    + "122.2 and 123.1. It does not claim the concrete A5 marked Phi, the "
                    + "U,V,D arrays, a normalizer cardinality, or any topology."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Statement()
    {
        Formula g = F.Id("G"), h = F.Id("H");
        Formula normalizer = Call("normalizer", h);
        Formula quotient = Call("quotientGroup", normalizer,
            Call("subgroupOf", h, normalizer));
        Formula omega = Call("rightCosetQuotient", h);
        Formula centralizer = Call("centralizerOfRightTranslations", omega, g);
        Formula body = Call("MulEquiv", quotient, centralizer);
        body = new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("H"), Call("Subgroup", g))],
            body);
        body = new Formula.TypeArrow(Call("Group", g), body);
        return Disp(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("G"), F.Id("Typeu"))],
            body));
    }
}
