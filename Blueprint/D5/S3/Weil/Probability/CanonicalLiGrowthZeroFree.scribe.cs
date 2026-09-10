using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Zeros.ActualZeroGeometryDocument;
using static StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability.AnalyticLogarithmicContinuationDocument;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class CanonicalLiGrowthZeroFreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/CanonicalLiGrowthZeroFree.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Use the merged derivative-defined canonical Li sequence to prove actual xi zero-freeness from an all-index growth condition.",
        H("CanonicalLiGrowthZeroFree"), Blocks(
            Describe.Lean(DescribeId.Create("canonical-li-series"),
                DeclarationHandle.Create(Prefix + "canonicalLiSeries"), H("The actual canonical coefficient sum"),
                StatementSource.FromAuthor(All("z", Complex, Equal(Call("canonicalLiSeries", Id("z")),
                    Sum(Multiply(Li(Add(Id("n"), Num(1))), Pow(Id("z"), Id("n"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficients are imported from CanonicalLiLocalExpansion. Their definition and indexing are unchanged."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("canonical-xi-disk"),
                DeclarationHandle.Create(Prefix + "canonicalXiDisk"), H("The actual xi function in disk coordinates"),
                StatementSource.FromAuthor(All("z", Complex, Equal(Call("canonicalXiDisk", Id("z")), Xi(Mobius(Id("z")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is precisely xiReading composed with the standard inverse Mobius coordinate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("canonical-xi-disk-analytic"),
                DeclarationHandle.Create(Prefix + "canonical_xi_disk_analytic"), H("Disk analyticity without a zero-location premise"),
                StatementSource.FromAuthor(AnalyticFormula(Id("canonicalXiDisk"), UnitDisk)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The entire original xiReading and the nonvanishing coordinate denominator prove analyticity on the entire unit disk."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-xi-disk-local-equation"),
                DeclarationHandle.Create(Prefix + "canonical_xi_disk_local_equation"), H("Consume the existing canonical local expansion"),
                StatementSource.FromAuthor(LocalEquation(Num(0), CanonicalEquation)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual derivative chain rule and the merged all-order local series give F'=GF near zero, using only xi(1)=1/2 to justify local cancellation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-li-summable-disk-zero-free"),
                DeclarationHandle.Create(Prefix + "canonical_li_summable_disk_zero_free"), H("Global disk equation and no zeros"),
                StatementSource.FromAuthor(Imp(AllSummable, And(AnalyticFormula(Id("canonicalLiSeries"), UnitDisk),
                    And(Disk(CanonicalEquation), DiskFree)))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Absolute convergence at every smaller radius makes the same scalar sum analytic. The local equation extends and analytic orders exclude every disk zero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("xi-disk-zero-free-right-half-plane"),
                DeclarationHandle.Create(Prefix + "xi_disk_zero_free_right_half_plane"), H("Bare disk to whole half-plane"),
                StatementSource.FromAuthor(Imp(DiskFree, HalfFree)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For Re(s)>1/2, set z=1-s inverse. The norm-square inequality puts z in the open disk and the inverse map returns s. No Li premise occurs."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("xi-disk-zero-free-implies-rh"),
                DeclarationHandle.Create(Prefix + "xi_disk_zero_free_implies_rh"), H("Bare disk converse to standard RH"),
                StatementSource.FromAuthor(Imp(DiskFree, RH)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The half-plane transfer feeds ActualZeroGeometry.rh_iff_xi_right_half_plane. Both existing summability consumers below use this bare bridge after disk nonvanishing."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-li-summable-right-half-plane"),
                DeclarationHandle.Create(Prefix + "canonical_li_summable_right_half_plane"), H("Actual open right-half-plane nonvanishing"),
                StatementSource.FromAuthor(Imp(AllSummable, HalfFree)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse Mobius point lies in the unit disk precisely in the direction needed. Its round trip recovers the original complex argument."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-li-disk-summability-implies-rh"),
                DeclarationHandle.Create(Prefix + "canonical_li_disk_summability_implies_rh"), H("The standard RiemannHypothesis conclusion"),
                StatementSource.FromAuthor(Imp(AllSummable, RH)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Existing actual xi-zero identification and right-half-strip reduction connect the no-zero result to Mathlib RiemannHypothesis. No supplied Li criterion is used."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-li-quadratic-growth-implies-rh"),
                DeclarationHandle.Create(Prefix + "canonical_li_quadratic_growth_implies_rh"), H("An explicit all-index growth condition suffices"),
                StatementSource.FromAuthor(All("C", Real, Imp(QuadraticBound, RH))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An absolute quadratic bound on every actual canonical coefficient supplies the required disk convergence. The arithmetic bound itself is not proved here."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-li-probability-envelope-implies-rh"),
                DeclarationHandle.Create(Prefix + "canonical_li_probability_envelope_implies_rh"), H("Consumer for the prior probability envelope"),
                StatementSource.FromAuthor(Imp(All("n", Natural, And(Le(Num(0), Li(Id("n"))),
                    Le(Li(Id("n")), Multiply(Li(Num(1)), Pow(Id("n"), Num(2)))))), RH)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input is the earlier probability route's exact output shape with its sequence identified as canonicalLiCoefficient. No candidate probability modules are copied into this branch."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("not-rh-forces-quadratic-escape"),
                DeclarationHandle.Create(Prefix + "not_rh_forces_quadratic_escape"), H("Every quadratic bound must fail under a failed RH"),
                StatementSource.FromAuthor(Imp(new Formula.Not(RH), All("C", Real, Exists("n", Natural,
                    Lt(Multiply(Id("C"), Pow(Id("n"), Num(2))), Abs(Li(Id("n")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The contrapositive produces an index exceeding any proposed absolute quadratic bound. It gives no finite cutoff for finding such an index."))), DescribeRole.Theorem))));
    internal static Formula Li(Formula n) => Call("canonicalLiCoefficient", n);
    internal static Formula Weighted(Formula radius) => Multiply(Abs(Li(Add(Id("n"), Num(1)))), Pow(radius, Id("n")));
    internal static Formula SummableAt(Formula radius) => Call("Summable", Lambda("n", Natural, Weighted(radius)));
    internal static Formula AllSummable => All("r", NNReal, Imp(Lt(Id("r"), Num(1)), SummableAt(Id("r"))));
    internal static Formula CanonicalEquation => Equal(Call("deriv", Id("canonicalXiDisk"), Id("z")),
        Multiply(Call("canonicalLiSeries", Id("z")), Call("canonicalXiDisk", Id("z"))));
    internal static Formula QuadraticBound => All("n", Natural,
        Le(Abs(Li(Id("n"))), Multiply(Id("C"), Pow(Id("n"), Num(2)))));
}
