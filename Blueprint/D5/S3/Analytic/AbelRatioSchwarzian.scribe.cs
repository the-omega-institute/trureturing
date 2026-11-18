using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class AbelRatioSchwarzianDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/AbelRatioSchwarzian.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Analytic/nist2010schwarzian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An Abel ratio of a nonvanishing second-order ODE solution has actual third-order regularity and an exact Schwarzian.",
        H("Schwarzian inference from ODE and Abel data"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-preschwarzian"),
                DeclarationHandle.Create(Prefix + "preSchwarzian"),
                H("The actual derivative quotient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a complex function t, preSchwarzian(t,x) is literally "
                    + "deriv(deriv t)(x) divided by deriv t(x). Nonvanishing and regularity "
                    + "are conclusions of the inference, rather than part of this definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-schwarzian"),
                DeclarationHandle.Create(Prefix + "schwarzian"),
                H("The classical Schwarzian convention"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("S(t)=t'''/t'-(3/2)(t''/t') squared, with all three "
                    + "derivatives the actual complex derivatives. This is the convention of DLMF 1.13.20."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("abel-ratio-schwarzian"),
                DeclarationHandle.Create(Prefix + "abel_ratio_schwarzian"),
                H("The inference, including second and third derivatives"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("On any open complex set U, assume y and its actual first derivative "
                        + "are differentiable, y is nonzero, p is differentiable, the nonzero Abel factor "
                        + "W has derivative -pW, t has derivative W/y squared, and "
                        + "y''+py'+qy=0. Then t' is nonzero. Writing L=y'/y and G=-p-2L, "
                        + "the theorem supplies HasDerivAt t' (G t'), and HasDerivAt t'' "
                        + "((-p'-2(-pL-q-L squared)+G squared)t'). It also proves "
                        + "t''/t'=G and S(t)=2q-p'-p squared/2.")),
                    Paragraph(Text("The proof first identifies t' with W/y squared on a neighborhood "
                        + "inside U. Quotient differentiation and the ODE give L'=-pL-q-L squared. "
                        + "A second neighborhood identity t''=Gt' then permits differentiation "
                        + "to the actual third derivative. No derivative of q or third derivative "
                        + "of y is a premise. The original half-binomial period is the live consumer. "
                        + "This formalizes a classical calculation and makes no literature novelty claim."))),
                DescribeRole.Theorem))));
}
