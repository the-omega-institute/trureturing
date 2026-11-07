using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier;

internal sealed class EJMOriginalPrefixDecoderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/EJMOriginalPrefixDecoder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Recover the complete original prefix from a valid partial assignment",
        H("Recover the complete original prefix from a valid partial assignment"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("The reader examines assigned prefix coordinates. Full equality of partial assignments additionally uses Valid, which excludes assignments at future coordinates; agreement on the observed prefix alone supplies only prefix agreement.")),
            Node("read-prefix", "readPrefix", "Read assigned values in base four",
                "Depth zero returns code zero. At the successor depth the reader combines the previous code with the value at coordinate depth, returning none if either the previous read or that coordinate is missing.", DescribeRole.Definition),
            Node("read-prefix-prefix-partial", "readPrefix_prefixPartial", "Read back the original prefix modulo its depth",
                "For every depth at most twenty and every natural code, reading prefixPartial yields that code modulo four to the depth. The proof preserves the previous prefix across the next coordinate update and combines quotient and remainder.", DescribeRole.Theorem),
            Node("read-prefix-eq-some-iff", "readPrefix_eq_some_iff", "Characterize a successful read in a valid context",
                "For depth at most twenty and Valid at fuel twenty-one minus depth with the given cache and partial assignment, a read yielding code is equivalent to code below four to the depth and equality of the entire partial assignment with prefixPartial at that depth and code. Private induction lemmas establish the read bound and prefix agreement; validity and future-none supply equality outside the prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
