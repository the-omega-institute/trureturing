using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class MiuraResidualCountDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/MiuraResidualCount.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/gupta2026miuradegrees");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact normalized height functions are counted with their full extrema and one common side.", H("The exact residual split count"),
        Blocks(
            Paragraph(Text("Chakshu Gupta, One construction for the Miura-ori flip-graph degree sequence, arXiv:2607.05567v3. The finite height suppliers are adapted from the accompanying CC BY 4.0 Lean source.")),
            Describe.Lean(DescribeId.Create("miuraresidualcount-allonside"),
                DeclarationHandle.Create(Prefix + "AllOnSide"), H("One common boundary side"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("This predicate uses one of four sides and one-based integer coordinates, and asks whether every member lies on that same side."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraresidualcount-residual"),
                DeclarationHandle.Create(Prefix + "Residual"), H("The exact residual class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The class imposes normalization, exact unit-edge increments, exact separate counts of all strict minima and maxima, and the absence of a single common boundary side containing all minima. Individual functions carry no symmetry quotient."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraresidualcount-residual-finite"),
                DeclarationHandle.Create(Prefix + "residual_finite"), H("Finiteness of the exact residual class"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The residual class is a subset of the finite set of normalized height functions. The proof supplies finiteness before its cardinality is taken."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("miuraresidualcount-residualcount"),
                DeclarationHandle.Create(Prefix + "residualCount"), H("Counting actual normalized functions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("This is the cardinality of the proved finite residual set. The positivity arguments establish a nonempty rectangle; they impose no extra restriction in the eventual counting region."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("miuraresidualcount-claim"),
                DeclarationHandle.Create(Prefix + "claim"), H("The full polynomial assertion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every natural split a+b=d with d at least five and 1 at most a at most b, one polynomial over the rationals in two variables is chosen before all natural dimensions m,n at least 2d-1. Its total degree is at most d-3, and its evaluations equal the exact residual counts. This definition states the entire assertion and supplies no proof of it."))), DescribeRole.Definition))));
}
