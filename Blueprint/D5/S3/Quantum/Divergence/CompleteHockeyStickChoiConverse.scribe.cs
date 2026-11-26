using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class CompleteHockeyStickChoiConverseDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full reference factor in the normalized Choi support characterizes strict complete hockey-stick contraction at each fixed parameter greater than one.",
        H("Strict complete hockey-stick contraction and Choi support"),
        Blocks(
          Describe.Lean(
            DescribeId.Create("complete-hockey-stick-choi-pure-replacement"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.exists_replacement_of_choi_support"),
            H("Pure replacement from full Choi support slices"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text(
                    "Let a finite CPTP channel have nonempty input. Suppose that for one nonzero "
                    + "output vector every reference basis slice of that vector lies in the range "
                    + "of the normalized Choi matrix. There exist a weight p strictly between zero "
                    + "and one, a pure output state, and a finite CPTP residual channel. On every "
                    + "input matrix, the channel is the sum of the residual with weight one minus "
                    + "p and trace times the pure state with weight p.")),
                Paragraph(Text(
                    "Normalize the output vector and assemble preimages of its slices under the "
                    + "positive Choi square root. A bound on their Gram matrix provides a strictly "
                    + "positive weight that can be subtracted while preserving Choi positivity. "
                    + "After dividing by one minus p, the remaining map is trace preserving. "
                    + "A finite Kraus representation gives the residual channel."))),
            DescribeRole.Theorem),
          Describe.Lean(
            DescribeId.Create("complete-hockey-stick-choi-support-implies-strict"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.coefficient_lt_one_of_choi_support"),
            H("Strict contraction from full Choi support slices"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "For every parameter at least one, a full reference factor over a nonzero output "
                + "vector implies that the complete coefficient for equal-reference-marginal "
                + "inputs is strictly below one. The constructed replacement weight p gives the "
                + "upper bound one minus p by the exhibited-weight bound from Proposition 31 "
                + "of George, Hirche, Nuradha and Wilde."))),
            DescribeRole.Theorem),
          Describe.Lean(
            DescribeId.Create("complete-hockey-stick-choi-strict-criterion"),
            DeclarationHandle.Create("D5/S3/Quantum/Divergence/CompleteHockeyStickChoiConverse.coefficient_lt_one_iff"),
            H("Choi support criterion for strict contraction"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(
                "For any finite CPTP channel with nonempty input and each fixed parameter greater "
                + "than one, the complete coefficient for equal-reference-marginal inputs is "
                + "strictly below one if and only if the normalized Choi support contains a full "
                + "reference factor over a nonzero output vector. In its absence the saturation "
                + "proof applies the classical-input support mechanism of Eriksson v3, Section 6, "
                + "through finite Bell preparations. In its presence the finite Choi residual "
                + "construction gives strict contraction. Both branches concern the static "
                + "channel and its Choi support."))),
            DescribeRole.Theorem))));
}
