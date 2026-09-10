using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Zeros.ActualZeroGeometryDocument;
using static StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability.AnalyticLogarithmicContinuationDocument;
using static StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability.CanonicalLiGrowthZeroFreeDocument;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class CanonicalLiRadiusObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/CanonicalLiRadiusObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual xi disk zero obstructs every eventual canonical coefficient envelope beyond its radius.",
        H("CanonicalLiRadiusObstruction"), Blocks(
            Describe.Lean(DescribeId.Create("scalar-series-analytic-of-eventual-bound"),
                DeclarationHandle.Create(Prefix + "scalar_series_analytic_of_eventual_bound"), H("An eventual bound controls the analytic radius"),
                StatementSource.FromAuthor(All("a", Function(Natural, Complex), All("R", NNReal, All("C", Real,
                    Imp(Eventual(Le(Multiply(Norm(Call("a", Id("n"))), Pow(Id("R"), Id("n"))), Id("C"))),
                        AnalyticFormula(ScalarSum, Call("ball", Num(0), Id("R")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pinned formal-series radius theorem uses the actual coefficients and permits an arbitrary finite initial segment."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-weighted-tail-bound-zero-free"),
                DeclarationHandle.Create(Prefix + "canonical_weighted_tail_bound_zero_free"), H("A tail envelope excludes actual disk zeros"),
                StatementSource.FromAuthor(All("R", NNReal, Imp(Lt(Num(0), Id("R")),
                    Imp(Le(Id("R"), Num(1)), All("C", Real, Imp(Eventual(Le(Weighted(Id("R")), Id("C"))),
                        All("z", Complex, Imp(Lt(Norm(Id("z")), Id("R")),
                            NotEqual(Call("canonicalXiDisk", Id("z")), Num(0)))))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At a positive radius at most one, the local actual-xi differential identity and the constructed analytic coefficient sum exclude every zero strictly inside that radius."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("disk-zero-forces-weighted-tail-escape"),
                DeclarationHandle.Create(Prefix + "disk_zero_forces_weighted_tail_escape"), H("Every tail exceeds every larger-radius envelope"),
                StatementSource.FromAuthor(All("z", Complex, Imp(Equal(Call("canonicalXiDisk", Id("z")), Num(0)),
                    TailEscape(Norm(Id("z")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A supplied actual disk zero forces unbounded weighted canonical coefficients in every tail. The radius is strictly larger than the zero modulus; no detection index bound is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("xi-zero-forces-weighted-tail-escape"),
                DeclarationHandle.Create(Prefix + "xi_zero_forces_weighted_tail_escape"), H("Retain the full actual xi zero coordinate"),
                StatementSource.FromAuthor(All("s", Complex, Imp(Equal(Xi(Id("s")), Num(0)),
                    TailEscape(Norm(Cayley(Id("s"))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same conclusion is stated directly for xiReading and its exact Mobius image. The zero is never replaced by only its imaginary part."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("disk-zero-forces-exponential-escape"),
                DeclarationHandle.Create(Prefix + "disk_zero_forces_exponential_escape"), H("An interior zero gives a strict exponential rate"),
                StatementSource.FromAuthor(Disk(Imp(Equal(Call("canonicalXiDisk", Id("z")), Num(0)),
                    Exists("R", NNReal, And(Lt(Norm(Id("z")), Id("R")),
                        And(Lt(Id("R"), Num(1)), All("N", Natural, All("C", Real, Escape)))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose a radius strictly between the zero modulus and one. At that radius every constant envelope is exceeded arbitrarily far out. Existence of an actual interior zero is not asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-canonical-weighted-envelopes"),
                DeclarationHandle.Create(Prefix + "rh_canonical_weighted_envelopes"), H("RH supplies a bound at each smaller radius"),
                StatementSource.FromAuthor(Imp(RH, AllEnvelopes)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete absolute canonical coefficient sum provides a nonnegative bound on every weighted coefficient. The constant may depend on the radius."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-smaller-radius-summable"),
                DeclarationHandle.Create(Prefix + "canonical_smaller_radius_summable"), H("A larger-radius bound gives smaller-radius summability"),
                StatementSource.FromAuthor(All("r", NNReal, All("R", NNReal, Imp(Lt(Id("r"), Id("R")),
                    All("C", Real, Imp(All("n", Natural, Le(Weighted(Id("R")), Id("C"))), SummableAt(Id("r")))))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proof retains the exact geometric factor (r/R) to compare the original absolute coefficient series with a convergent majorant."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-iff-canonical-weighted-envelopes"),
                DeclarationHandle.Create(Prefix + "rh_iff_canonical_weighted_envelopes"), H("All-radius envelopes are equivalent to RH"),
                StatementSource.FromAuthor(Iff(RH, AllEnvelopes)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every radius below one there must be a bound for all indices. No radius-independent constant, finite cutoff or unconditional arithmetic bound is supplied."))), DescribeRole.Theorem))));
    private static Formula Eventual(Formula body) => Exists("N", Natural,
        All("n", Natural, Imp(Le(Id("N"), Id("n")), body)));
    private static Formula Escape => Exists("n", Natural,
        And(Le(Id("N"), Id("n")), Lt(Id("C"), Weighted(Id("R")))));
    private static Formula TailEscape(Formula modulus) => All("R", NNReal,
        Imp(Lt(modulus, Id("R")), Imp(Le(Id("R"), Num(1)), All("N", Natural, All("C", Real, Escape)))));
    private static Formula AllEnvelopes => All("R", NNReal, Imp(Lt(Id("R"), Num(1)),
        Exists("C", Real, And(Le(Num(0), Id("C")), All("n", Natural, Le(Weighted(Id("R")), Id("C")))))));
}
