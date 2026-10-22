using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BesselRedheffer;

internal sealed class FirstZeroDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positivity before the first zero and a radial trial-function estimate.",
        H("The first positive zero"), Blocks(
            Entry("bessel-positive-before-zero", "nbessel_pos_of_lt", "Positivity before the first zero",
                "For order nu greater than -1 and 0 less than or equal to x less than the first positive zero, the normalized series is positive at x. If it were nonpositive, continuity and its value one at zero would produce a positive zero no greater than x, contradicting the defining infimum."),
            Entry("bessel-energy", "nbessel_energy_bound", "The radial trial-function estimate",
                "For nu at least thirty, if the normalized series is positive on the closed interval from zero to a positive z, then z squared is at most (6/5)(nu+1)(nu+7). With y(r) equal to the series at zr, weight w(r)=r to the power 2nu+1, logarithmic derivative h=y prime/y, and trial function u(r)=(1-r squared) cubed, the weighted square of u prime minus hu integrates to the energy minus z squared times the weighted norm. The boundary term vanishes. Expanding the two polynomial factors and integrating powers gives the energy equal to (6/5)(nu+1)(nu+7) times the weighted norm. The norm is strictly positive."),
            Entry("bessel-first-zero-positive", "firstZero_pos", "The infimum is positive",
                "For nu at least thirty, a positive zero exists: otherwise positivity would hold on arbitrarily long intervals, contradicting the energy estimate. Positivity in a neighbourhood of zero gives a strictly positive lower bound on all positive zeros and hence on their infimum."),
            Entry("bessel-first-zero-vanishes", "nbessel_firstZero", "The infimum is a zero",
                "For nu at least thirty, the set of positive zeros is nonempty, bounded below and closed. It is closed because continuity makes the zero set closed and the value one at the origin excludes zero. The infimum therefore belongs to the set."),
            Entry("bessel-first-zero-bound", "firstZero_sq_le", "An upper bound for the first zero",
                "For every real nu at least thirty, the first positive zero squared is at most (6/5)(nu+1)(nu+7). If it were larger, an argument strictly between the square root of this bound and the first zero would have positivity throughout its closed initial interval, contradicting the energy estimate."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/BesselRedheffer/FirstZero." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
