using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Forbidden;

internal sealed class NaimiCyclicWordReplacementDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent compatibility does not guarantee positional cyclic replacement in finite linear words.",
        H("Cyclic replacement of adjacent-compatible words"),
        Blocks(
            Describe.Lean(DescribeId.Create("naimi-positional-replacement-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Positional replacement by a bijection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Section 8 of Ramin Naimi's Swapping Compatible Words, "
                        + "arXiv:2610.31967v2, asks for a cyclic replacement of three or more "
                        + "patterns. The labels have successor i + 1 modulo the cycle size, "
                        + "and patterns may repeat.")),
                    Paragraph(Text("The directed border lengths from one pattern to another "
                        + "are the lengths at which a suffix of the first equals a prefix of "
                        + "the second. Length zero is always a border. For words of the same "
                        + "length, full length is a border exactly when the words are identical. "
                        + "Adjacent labels have equal self-border sets and equal directed "
                        + "sets in the two directions. Equality of the self-border sets "
                        + "forces a common pattern length.")),
                    Paragraph(Text("For each host length the claim asks for a single bijection "
                        + "on all hosts over the given finite alphabet. For every host, label, "
                        + "and zero-based start, the input has that occurrence exactly when "
                        + "the output has the successor occurrence at the same start. An "
                        + "occurrence lies on a nonempty interval inside the host, so an empty "
                        + "pattern has no occurrences. The same-position equivalence follows "
                        + "the two-pattern swap definition in Section 2.3, PDF p. 5. "
                        + "https://arxiv.org/html/2610.31967v2#S2.SS3.p4.1"))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("naimi-positional-replacement-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Four patterns force conflicting letters"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Use 001, 002, 011 and 021 in that cyclic order over "
                        + "the alphabet of 0, 1 and 2. Every self-border set is {0, 3}. "
                        + "Every adjacent directed border set is {0} in either direction. "
                        + "In particular, the forward edges have the common set {0} "
                        + "required by the alternative in Section 8.")),
                    Paragraph(Text("The host 0021 contains 002 at start 0 and 021 at start 1. "
                        + "One output would have to contain 011 at start 0 and 001 at "
                        + "start 1. Offset 1 of the first demand forces the letter 1 at "
                        + "coordinate 1, and offset 0 of the second forces the letter 0 there."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("naimi-2026-cyclic-compatible-word-replacement"),
                    ResolutionKind.Refuted)))));
}
