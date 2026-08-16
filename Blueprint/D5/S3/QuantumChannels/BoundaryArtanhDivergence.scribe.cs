using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class BoundaryArtanhDivergenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed-state logarithmic tax diverges at the pure-state boundary.",
        H("Boundary Artanh Divergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("logarithmic-tax-diverges-at-boundary"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumChannels/BoundaryArtanhDivergence."
                    + "logarithmic_tax_diverges_at_boundary"),
                H("The logarithmic tax diverges at the boundary"),
                StatementSource.FromAuthor(Disp(Seq(
                    Lim, Underscore, Grp(F.Id("r"), To, D(1), Caret, Grp(Minus)), Sp,
                    Frac,
                    Grp(F.Id("r"), Cdot, Operatorname, Grp(F.Id("artanh")),
                        Open, F.Id("r"), Close),
                    Grp(D(2)), Sp, Eq, Sp, Infty, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "As the mixed-state radius r approaches one from below, the coefficient "
                        + "r artanh(r) / 2 diverges to positive infinity. The proof first uses "
                        + "artanh(tanh b) = b and strict monotonicity of artanh to establish the "
                        + "boundary divergence of artanh itself. It then combines that divergence "
                        + "with the limiting positive factor r / 2.")),
                    Paragraph(Text(
                        "This closes only the boundary clause c(r) = r artanh(r) / 2 with its "
                        + "logarithmic divergence in source atom appendix/E.173. It does not claim "
                        + "the atom's multiparameter budget, pure-state balancing, or metric-family "
                        + "classification statements."))),
                DescribeRole.Theorem))));
}
