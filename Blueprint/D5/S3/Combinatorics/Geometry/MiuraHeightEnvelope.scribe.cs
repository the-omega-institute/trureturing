using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraHeightEnvelopeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraHeightEnvelope.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite unit-edge height arrays have attained extremum envelopes and finitely many normalized representatives.", H("Finite height envelopes"),
        Blocks(
            Paragraph(Text("Chakshu Gupta, One construction for the Miura-ori flip-graph degree sequence, arXiv:2607.05567v3. The finite height suppliers are adapted from the accompanying CC BY 4.0 Lean source.")),
            Describe.Lean(DescribeId.Create("miuraheightenvelope-isheight"),
                DeclarationHandle.Create(Prefix + "IsHeight"), H("Unit-edge heights"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("A source cell with one-based coordinates corresponds to its coordinates minus one in Fin m times Fin n. Every actual grid edge has absolute height difference exactly one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraheightenvelope-isstrictlocalmin"),
                DeclarationHandle.Create(Prefix + "IsStrictLocalMin"), H("Strict minima"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every existing adjacent cell is one higher. Physical boundary points use all their existing neighbours."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraheightenvelope-isstrictlocalmax"),
                DeclarationHandle.Create(Prefix + "IsStrictLocalMax"), H("Strict maxima"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Every existing adjacent cell is one lower. There is no imposed boundary extension."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraheightenvelope-envelope-min"),
                DeclarationHandle.Create(Prefix + "envelope_min"), H("The attained finite minimum envelope"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Each value equals the height of some actual strict minimum plus Manhattan distance, and is bounded above by the corresponding cone from every strict minimum. Finiteness supplies descent termination."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraheightenvelope-envelope-max"),
                DeclarationHandle.Create(Prefix + "envelope_max"), H("The attained finite maximum envelope"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Negation gives the dual attained maximum of downward cones. The finite grid remains the same actual height array."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraheightenvelope-canonicalheights-finite"),
                DeclarationHandle.Create(Prefix + "CanonicalHeights_finite"), H("Finitely many normalized heights"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("On a nonempty rectangle normalization at the origin and the unit-edge bound put every integer value in a fixed finite interval. The resulting finite product contains all normalized height functions."))), DescribeRole.Theorem))));
}
