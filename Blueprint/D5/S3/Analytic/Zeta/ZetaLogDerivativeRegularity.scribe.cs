using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Zeta;

internal sealed class ZetaLogDerivativeRegularityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Zeta/ZetaLogDerivativeRegularity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing the pole of zeta at one before taking its logarithmic derivative "
            + "gives a principal term regular on the nonnegative real axis. "
            + "The translated nontrivial zeros have negative half-integer residues.",
        H("The normalized zeta logarithmic derivative"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-real-normalized-zeta"),
                DeclarationHandle.Create(Prefix + "normalized_zeta_ne_zero_real"),
                H("The normalized zeta factor has no positive real zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The entire completion Z(s) of (s-1)zeta(s) is nonzero "
                    + "at every positive real s. Away from one this follows from "
                    + "the sign of real zeta; at one its value is one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cancelled-principal-expression"),
                DeclarationHandle.Create(Prefix + "regularizedPrincipal_eq"),
                H("Cancellation of the density pole"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let Z(s) be the entire completion of (s-1)zeta(s). "
                    + "At a point s different from one half where zeta(s+1/2) is nonzero, "
                    + "the quantity -Z'(s+1/2)/(2Z(s+1/2)) equals "
                    + "-zeta'(s+1/2)/(2zeta(s+1/2))-1/(2(s-1/2))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonnegative-real-regularity"),
                DeclarationHandle.Create(Prefix + "regularizedPrincipal_analyticAt_real"),
                H("Regularity along the nonnegative real axis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonnegative real sigma, the cancelled principal term "
                    + "is complex analytic near sigma. Zeta has no real zero between zero "
                    + "and one, has no zero to the right of one, and Z(1)=1. "
                    + "These facts include regularity at sigma=0 and sigma=1/2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("isolated-translated-zeros"),
                DeclarationHandle.Create(Prefix + "normalized_zeta_eventually_ne_zero"),
                H("Isolation of translated nontrivial zeros"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nontrivial zeta zero rho, the function Z(s+1/2) "
                    + "is nonzero in a punctured neighborhood of rho-1/2. "
                    + "The local factorization into a positive integer power "
                    + "times an analytic nonvanishing function gives the isolation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("translated-zero-residue"),
                DeclarationHandle.Create(Prefix + "regularizedPrincipal_zero_residue"),
                H("Multiplicity determines the translated residue"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nontrivial zeta zero rho there is a positive integer m "
                    + "such that (s-(rho-1/2)) times the cancelled principal term "
                    + "tends to -m/2 as s approaches rho-1/2 through distinct points. "
                    + "The analytic-unit factorization of zeta supplies m; the "
                    + "subtracted density term is regular at this translated zero."))),
                DescribeRole.Theorem))));
}
