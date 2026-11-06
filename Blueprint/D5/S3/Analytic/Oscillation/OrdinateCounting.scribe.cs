using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Oscillation;

internal sealed class OrdinateCountingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Oscillation/OrdinateCounting.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted counts and triangular averages of a locally finite positive spectrum.",
        H("Counting positive ordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-gap"),
                DeclarationHandle.Create(Prefix + "positive_gap"),
                H("Separation from zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let gamma be a family of distinct positive real ordinates, with only "
                    + "finitely many ordinates below each real bound. There exists b>0 such "
                    + "that every ordinate is greater than b. A positive minimum for the "
                    + "finite set below one, together with the bound one for its complement, "
                    + "gives the gap."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("lower-triangular-mass"),
                DeclarationHandle.Create(Prefix + "lower_triangular_mass"),
                H("Triangular lower mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Give each ordinate a positive integer multiplicity and write N(T) "
                    + "for the total multiplicity at ordinates at most T. If "
                    + "N(T)/(T log T) tends to 1/(2 pi), then the sum of multiplicities "
                    + "weighted by max(0,1-gamma/M), divided by M log M, tends to "
                    + "1/(4 pi). The triangular sum is the integral of N(Mu) for "
                    + "0<u<=1. After normalization, the integrand tends to u/(2 pi); "
                    + "monotonicity of N supplies a constant integrable bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("select-upper-band"),
                DeclarationHandle.Create(Prefix + "select_upper_band"),
                H("An upper band with substantial triangular mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Assume N(T)/(T log T) tends to 1/(2 pi). For every fixed b>0 "
                    + "there is a constant cb>0 such that, for all sufficiently large T, "
                    + "some U in [T,2T] has triangular mass Wplus(b,U) at least cb log T. "
                    + "The total multiplicity at ordinates with abs(gamma-U)<b is at most "
                    + "twelve times that triangular mass. One may take cb=b/(200 pi). "
                    + "Integrate the two finite sums over the centers in [T,2T]. Each "
                    + "counting window contributes at most 2b. The middle half of each "
                    + "triangle contributes at least b/2, and the ordinates between "
                    + "17T/16 and 31T/16 supply enough total multiplicity. If every "
                    + "center failed one of the two inequalities, integration would "
                    + "contradict these bounds. No local counting estimate is assumed."))),
                DescribeRole.Theorem))));
}
