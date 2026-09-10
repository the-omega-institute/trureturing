using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Zeros.ActualZeroGeometryDocument;
using static StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability.AnalyticLogarithmicContinuationDocument;
using static StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability.CanonicalLiGrowthZeroFreeDocument;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Probability;

internal sealed class CanonicalLiDiskEquivalenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Probability/CanonicalLiDiskEquivalence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual canonical Li series has a full-disk convergence criterion equivalent to the standard Riemann hypothesis.",
        H("CanonicalLiDiskEquivalence"), Blocks(
            Describe.Lean(DescribeId.Create("disk-mobius-re-half"),
                DeclarationHandle.Create(Prefix + "disk_mobius_re_half"), H("Disk points map to the actual right half-plane"),
                StatementSource.FromAuthor(Disk(Lt(OneHalf, Call("Re", Mobius(Id("z")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The strict real-part inequality is derived from the original complex norm and the positive inverse denominator."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-xi-disk-ne-zero"),
                DeclarationHandle.Create(Prefix + "rh_xi_disk_ne_zero"), H("RH supplies actual disk nonvanishing"),
                StatementSource.FromAuthor(Imp(RH, DiskFree)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing xi/nontrivial-zero identity and the standard RiemannHypothesis predicate exclude a zero in the disk image."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("canonical-xi-disk-def"),
                DeclarationHandle.Create(Prefix + "canonical_xi_disk_def"), H("Definitional adapter to literal xi"),
                StatementSource.FromAuthor(All("z", Complex, Equal(Call("canonicalXiDisk", Id("z")), Xi(Mobius(Id("z")))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original disk definition is retained in Growth."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("xi-right-half-plane-zero-free-disk"),
                DeclarationHandle.Create(Prefix + "xi_right_half_plane_zero_free_disk"), H("Half-plane to disk"),
                StatementSource.FromAuthor(Imp(HalfFree, DiskFree)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This direction uses the existing disk_mobius_re_half."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("xi-disk-zero-free-iff-right-half-plane"),
                DeclarationHandle.Create(Prefix + "xi_disk_zero_free_iff_right_half_plane"), H("Both geometric directions"),
                StatementSource.FromAuthor(Iff(DiskFree, HalfFree)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both domains are open and contain every qualifying complex point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-iff-canonical-xi-disk-ne-zero"),
                DeclarationHandle.Create(Prefix + "rh_iff_canonical_xi_disk_ne_zero"), H("A005 with the original disk definition"),
                StatementSource.FromAuthor(Iff(RH, DiskFree)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original RH forward proof is combined with Growth's bare converse."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-iff-xi-disk-ne-zero"),
                DeclarationHandle.Create(Prefix + "rh_iff_xi_disk_ne_zero"), H("A005 in literal source coordinates"),
                StatementSource.FromAuthor(Iff(RH, LiteralDiskFree)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("No Li summability premise occurs in either direction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-zero-geometry-disk-spec"),
                DeclarationHandle.Create(Prefix + "actual_zero_geometry_disk_spec"), H("A001 through A005, each as a full iff"),
                StatementSource.FromAuthor(And(Iff(RH, OnLine), And(Iff(RH, CentralReal),
                    And(Iff(RH, HalfFree), And(Iff(RH, CayleyUnit), Iff(RH, LiteralDiskFree)))))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The lower owner supplies A001-A004. RH retains Mathlib's exceptional-zero and s!=1 quantifiers; xiReading is the actual entire function. This package does not establish RH, the larger E1/P0 atoms, or the remaining atlas."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-li-generator-analytic"),
                DeclarationHandle.Create(Prefix + "rh_li_generator_analytic"), H("The existing generator is analytic on the disk"),
                StatementSource.FromAuthor(Imp(RH, AnalyticFormula(Id("liGenerator"), UnitDisk))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("RH is used only in this forward direction to justify the actual logarithmic derivative everywhere in the disk."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-canonical-li-global-expansion"),
                DeclarationHandle.Create(Prefix + "rh_canonical_li_global_expansion"), H("Globalize the proved canonical Taylor coefficients"),
                StatementSource.FromAuthor(Imp(RH, Disk(Expansion))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The merged all-order coefficient identification is inserted into the standard holomorphic Taylor theorem. No coefficients are redefined."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-canonical-li-disk-summable"),
                DeclarationHandle.Create(Prefix + "rh_canonical_li_disk_summable"), H("Absolute convergence at every radius below one"),
                StatementSource.FromAuthor(Imp(RH, AllSummable)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite-dimensional absolute summability converts the full complex Taylor series into the original weighted absolute coefficient sum."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-iff-canonical-li-disk-summable"),
                DeclarationHandle.Create(Prefix + "rh_iff_canonical_li_disk_summable"), H("Close both directions of the canonical criterion"),
                StatementSource.FromAuthor(Iff(RH, AllSummable)), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The forward proof is combined with the prior analytic-order converse. Neither the arithmetic condition nor RH is asserted unconditionally."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rh-iff-canonical-li-global-expansion"),
                DeclarationHandle.Create(Prefix + "rh_iff_canonical_li_global_expansion"), H("The actual full-disk expansion is equivalent to RH"),
                StatementSource.FromAuthor(Iff(RH, Disk(Expansion))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The conclusion concerns every point of the full disk, not a local germ or a finite coefficient prefix."))), DescribeRole.Theorem))));
    private static Formula Expansion => Call("HasSum", Lambda("n", Natural,
        Multiply(Li(Add(Id("n"), Num(1))), Pow(Id("z"), Id("n")))), Call("liGenerator", Id("z")));
}
