using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization;

internal sealed class UnimodularMonomialSubstitutionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant-one monomial substitution has an explicit inverse on nonzero pairs.",
        H("Unimodular Monomial Substitution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unimodular-monomial-substitution"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/UnimodularMonomialSubstitution.unimodular_monomial_substitution"),
                H("The substitution is inverted by two monomials"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("P"), Sp, Eq, Sp, F.Id("u"), Caret, Grp(D(2)), Sp, Slash, Sp, F.Id("v"),
                    Comma, Sp,
                    F.Id("Q"), Sp, Eq, Sp, F.Id("v"), Caret, Grp(D(2)), Sp, Slash, Sp,
                    F.Id("u"), Caret, Grp(D(3)), Comma, Sp,
                    F.Id("u"), Sp, Neq, Sp, D(0), Comma, Sp,
                    F.Id("v"), Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    F.Id("P"), Caret, Grp(D(2)), F.Id("Q"), Sp, Eq, Sp, F.Id("u"),
                    Sp, Land, Sp,
                    F.Id("P"), Caret, Grp(D(3)), F.Id("Q"), Caret, Grp(D(2)),
                    Sp, Eq, Sp, F.Id("v"), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source atom explicitly displays the change of variables P = u^2/v "
                        + "and Q = v^2/u^3 and calls its exponent matrix determinant one. This "
                        + "partial closure isolates exactly the resulting inverse formula on the "
                        + "nonzero coordinate domain.")),
                    Paragraph(Text(
                        "Substitution reduces the first recovered coordinate to u^4 v^2 divided "
                        + "by v^2 u^3, and the second to u^6 v^4 divided by v^3 u^6. The nonzero "
                        + "hypotheses discharge both denominators.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proving. No exact theorem for this "
                        + "monomial substitution was found; the proof uses its field normalizer "
                        + "for the component identities."))),
                DescribeRole.Theorem)),
        []));
}
