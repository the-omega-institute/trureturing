using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class ThresholdSchurSemigroupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Semigroups/ThresholdSchurSemigroup.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exponential absolute-distance Schur evolution on any finite labelled matrix algebra is a continuous CPTP scale semigroup with a finite threshold generator.",
        H("Finite Label Threshold Evolution"),
        Blocks(
            Paragraph(Text(
                "Take any finite type of logical labels and any real value a(s) on each label. "
                + "Every original label is retained, including repeated values. At real scale u the "
                + "matrix entry (s,t) is multiplied by exp(-u abs(a(s)-a(t))/2). "
                + "The completely positive trace-preserving channels are constructed for u>=0. "
                + "The entry formula also defines the differentiable extension on the full real line.")),
            Describe.Lean(
                DescribeId.Create("threshold-evolution"), DeclarationHandle.Create(Prefix + "evolution"),
                H("Logical matrix evolution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed logical carrier supports all input matrices, not only diagonal states or populations."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("distinct-label-image"), DeclarationHandle.Create(Prefix + "labelSet"),
                H("Distinct label image"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite image contains each distinct real label value exactly once."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("ordered-threshold-data"), DeclarationHandle.Create(Prefix + "ThresholdData"),
                H("Ordered distinct image data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The data contain a monotonically extended sequence, strictly increasing on its "
                    + "first count+1 entries, and a rank map retaining every original label. "
                    + "Every site belongs to the label image when the carrier is nonempty. "
                    + "The number of cuts is the image cardinality minus one, truncated at zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("canonical-thresholds"), DeclarationHandle.Create(Prefix + "thresholds"),
                H("Increasing image choice"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose the proved ordered image data; an empty carrier uses zero cuts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("threshold-projection"), DeclarationHandle.Create(Prefix + "projection"),
                H("Threshold projections"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Sort the distinct image of a in increasing order. For each adjacent pair, "
                    + "the projection is diagonal with entry one exactly when the original label "
                    + "value is at or below the lower site. The gap is the next site minus the "
                    + "current site. An all-equal family has no thresholds."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("adjacent-threshold-gap"), DeclarationHandle.Create(Prefix + "gap"),
                H("Adjacent gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The gap is the upper adjacent image value minus the lower one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("threshold-generator"), DeclarationHandle.Create(Prefix + "generator"),
                H("Finite threshold generator"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Sum gap(i) times P(i) X P(i) minus one half of P(i) X + X P(i). "
                    + "The generator superoperator matrix is diagonal in the matrix-unit basis "
                    + "indexed by ordered logical-label pairs."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("generator-matrix"), DeclarationHandle.Create(Prefix + "generatorMatrix"),
                H("Generator in matrix-unit coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The superoperator matrix indexed by pairs of original labels is diagonal, "
                    + "with diagonal value minus half their absolute real-label separation."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("threshold-semigroup"), DeclarationHandle.Create(Prefix + "result"),
                H("CPTP semigroup, exact rates and exponential"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There is a family of canonical QuantumChannel maps at every nonnegative "
                        + "real scale with exactly the stated action on every logical matrix. "
                        + "The channels compose by adding scales, and the zero-scale bundled "
                        + "linear map is the identity. Every matrix trajectory is continuous. "
                        + "Each gap is nonnegative, and each threshold matrix is self-adjoint "
                        + "and idempotent.")),
                    Paragraph(Text(
                        "The generator multiplies entry (s,t), and hence matrix unit E(s,t), "
                        + "by -abs(a(s)-a(t))/2. The evolution is the actual matrix exponential "
                        + "of u times this generator in matrix-unit coordinates. Its derivative "
                        + "at every real scale is the generator applied to the evolved matrix. "
                        + "Equal-value blocks have zero rate, zero scale preserves every entry, "
                        + "and a single distinct value gives identity evolution.")),
                    Paragraph(Text(
                        "For a binary threshold p and q in [0,1], three diagonal Kraus operators "
                        + "are sqrt(q) I, sqrt(1-q) P and sqrt(1-q) (I-P). Their squares sum to "
                        + "the identity. The factor preserves entries on each side of the cut "
                        + "and multiplies separated entries by q. Composing the factors with "
                        + "q=exp(-u gap/2) gives the claimed channel. The sum of exactly the "
                        + "separating adjacent gaps telescopes to the absolute label separation. "
                        + "This same identity evaluates the finite generator sum.")),
                    Paragraph(Text(
                        "The parameter is scale, not physical time. This fixed logical-algebra "
                        + "construction supplies no encoding of a noninteger Schmidt rank. "
                        + "For the integer-rank tower of ARITHMETIC_HOLOGRAPHIC_RT section 34.3, "
                        + "set a(s)=log(b(s)) and compare at integer differences n-j. An actual "
                        + "flat physical channel correspondence and its optimality are separate "
                        + "requirements; this theorem does not establish the integer physical "
                        + "tower, its endpoint partial traces or the asymptotic optimum."))),
                DescribeRole.Theorem))));
}
