using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.FourthTransfer;

internal sealed class FourthMomentAsymptoticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthTransfer/FourthMomentAsymptotic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform cumulative fourth-moment asymptotics give band and local energy estimates.",
        H("Cumulative fourth-moment asymptotics"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("band-lengths"),
                DeclarationHandle.Create(Prefix + "band_lengths"),
                H("Band lengths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Y>=1 and 0<alpha<beta<1, every length between Y^alpha and Y^beta lies between one and Y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("band-log-lower"),
                DeclarationHandle.Create(Prefix + "band_log_lower"),
                H("Band log lower"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive Y and v with v<=Y^beta, log(Y/v) is at least (1-beta) log Y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-ratio-abs-le"),
                DeclarationHandle.Create(Prefix + "log_ratio_abs_le"),
                H("Log ratio abs le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 1<=v<=Y and 1<=y<=Y, the absolute value of log(y/v) is at most log Y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-square-integrable"),
                DeclarationHandle.Create(Prefix + "log_square_integrable"),
                H("Log square integrable"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<a<=b and v>0, the square of log(y/v)+B is interval integrable from a to b."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("log-square-integral-le"),
                DeclarationHandle.Create(Prefix + "log_square_integral_le"),
                H("Log square integral le"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 0<a<=b and v>0, if |log(y/v)+B|<=T throughout [a,b] with T>=0, its squared integral is at most (b-a) T^2."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fourth-moment-asymptotic-for"),
                DeclarationHandle.Create(Prefix + "FourthMomentAsymptoticFor"),
                H("The uniform cumulative formula"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every eta>0, one threshold in Y works for every Y^alpha<=v<=Y^beta: "
                    + "the absolute difference between the integral of |E(x+v)-E(x)|^4 over [1,Y] "
                    + "and 3*v^2 times the integral of (log(y/v)+B)^2 over [1,Y] is at most "
                    + "eta*Y*v^2*log(Y/v)^2. The threshold is independent of v."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("asymptotic-implies-band"),
                DeclarationHandle.Create(Prefix + "asymptotic_implies_band"),
                H("The fourth-moment band bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Suppose E is locally bounded and measurable and 0<alpha<beta<1. "
                    + "The uniform cumulative formula implies the existence of a nonnegative C "
                    + "such that the fourth moment is at most C*Y*v^2*log(Y/v)^2 "
                    + "for all sufficiently large Y and all lengths in the exponent band. "
                    + "On [1,Y], the bounds 1<=v<=Y give |log(y/v)|<=log(Y), while "
                    + "log(Y/v)>=(1-beta)*log(Y). One may take "
                    + "C=3*((1+|B|)/(1-beta))^2+1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("asymptotic-implies-local"),
                DeclarationHandle.Create(Prefix + "asymptotic_implies_local"),
                H("Local fourth energy with constant thirteen"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same assumptions, there is a nonnegative epsilon(X) tending "
                        + "to zero such that, for all sufficiently large X, simultaneously for "
                        + "X/2<=A<=B<=4X and (4X)^alpha<=v<=(X/2)^beta, the integral "
                        + "of |E(y+v)-E(y)|^4 over [A,B] is at most "
                        + "13*v^2*log(X)^2*(B-A+epsilon(X)*X).")),
                    Paragraph(Text(
                        "The length v lies in the exponent band at both cumulative endpoints. "
                        + "Subtract the formulas at B and A. Their main terms differ by the "
                        + "integral over [A,B], where 0<=log(y/v)<=2*log(X). Once "
                        + "log(X)>=20*|B|, three times (2*log(X)+|B|)^2 is at most "
                        + "13*log(X)^2. Each cumulative error is at most "
                        + "16*delta*X*v^2*log(X)^2; delta=13*eta/32 gives the window "
                        + "bound with any prescribed eta>0. Taking an infimum of admissible "
                        + "nonnegative window errors and adding 1/max(1,X) produces a single "
                        + "nonnegative error function tending to zero."))),
                DescribeRole.Theorem))));
}
