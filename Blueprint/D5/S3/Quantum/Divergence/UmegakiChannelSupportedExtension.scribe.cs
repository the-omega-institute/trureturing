using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class UmegakiChannelSupportedExtensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/UmegakiChannelSupportedExtension.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/hirchegeorgenuradhawilde2026conditional");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The supported entropy coefficients coincide and are attained by the left endpoint of the arithmetic metric family.",
        H("Complete and conditional Umegaki coefficients"), Blocks(
            Describe.Lean(DescribeId.Create("completecoefficient"),
                DeclarationHandle.Create(Prefix + "completeCoefficient"),
                H("Complete Umegaki coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take the supremum of supported Umegaki output-to-input ratios over every finite quantum reference and all joint density pairs with equal reference marginals and strictly positive finite input entropy. Adjoin zero to give the empty ratio set coefficient zero."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("conditionalcoefficient"),
                DeclarationHandle.Create(Prefix + "conditionalCoefficient"),
                H("Conditional Umegaki coefficient"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Allow arbitrary supported joint density pairs and subtract the respective marginal divergences at input and output. Require a strictly positive finite input deficit. The actual output marginals equal the input marginals by trace preservation, and data processing makes every term finite on the admitted branch."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("depolarized-endpointbound-completecoefficient"),
                DeclarationHandle.Create(Prefix + "depolarized_endpointBound_completeCoefficient"),
                H("Entropy controls the faithful endpoint tests"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Approximate every nonzero left-endpoint test of a genuinely output-depolarized channel with actual equal-marginal density pairs. Data processing bounds the depolarized ratio by the ratio for the original channel on the same pairs. The supremum then bounds the endpoint test, including the separate zero-form case."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("supported-conditional-relativeentropy-contraction"),
                DeclarationHandle.Create(Prefix + "supported_conditional_relativeEntropy_contraction"),
                H("Contraction at the support boundary"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A uniform endpoint bound on genuine output depolarizations contracts the supported conditional deficit for the original channel. At fixed output depolarization first remove common replacement noise at the input. Then remove output noise using each state's own reference marginal. The same CPTP map acts on both states in each step, supplying the upper bounds needed for the supported limits."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conditionalcoefficient-eq-completecoefficient"),
                DeclarationHandle.Create(Prefix + "conditionalCoefficient_eq_completeCoefficient"),
                H("Equality on the finite support branch"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For each finite CPTP channel the complete and conditional Umegaki coefficients coincide. This rules out the relative-entropy instance of the strict separation asked in the second bullet of §9 of Hirche, George, Nuradha and Wilde, arXiv:2608.27171v1. Definition 2, Eqs. (2.13) and (2.14), and Remark 2 determine the ratios and the positive finite denominator convention.")),
                    Paragraph(Text("The equal-marginal ratios embed into the conditional ratios. The faithful endpoint approximation and ordered support limits give the reverse bound. Squared trace distance supplies the separate strict separation in FaithfulConditionalGap.result."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("variationalinverse-channel-contraction"),
                DeclarationHandle.Create(Prefix + "variationalInverse_channel_contraction"),
                H("Actual finite arithmetic inverse form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a positive semidefinite joint base, a complex direction of zero partial trace, and 0 ≤ t ≤ 1, boundedness of the input quadratic tests implies boundedness at the actual amplified output. The output supremum is at most the complete entropy coefficient times the input supremum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("variationalmetriccoefficient"),
                DeclarationHandle.Create(Prefix + "variationalMetricCoefficient"),
                H("Arithmetic metric coefficient at t"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take ratios over every finite reference, faithful correlated input bases and complex zero-partial-trace directions of positive input inverse form. Use the actual output variational form and adjoin zero before taking the supremum. The supported Moore–Penrose form is its exact output representation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("variationalmetriccoefficient-bounds"),
                DeclarationHandle.Create(Prefix + "variationalMetricCoefficient_bounds"),
                H("Upper bound at each parameter"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every t in the closed unit interval, the actual metric coefficient lies between zero and the complete Umegaki coefficient."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("variationalmetriccoefficient-chain"),
                DeclarationHandle.Create(Prefix + "variationalMetricCoefficient_chain"),
                H("Left endpoint and the metric supremum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The left-endpoint coefficient c₀ equals the complete coefficient ηᶜ, which equals the conditional coefficient ηΔ, which equals sup over 0 ≤ t ≤ 1 of cₜ. A comparison with output depolarizations makes c₀ a uniform endpoint bound and supplies the reverse entropy inequality."))),
                DescribeRole.Theorem))));
}
