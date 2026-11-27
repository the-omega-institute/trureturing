using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class BesselSystemDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bessel System", H("Bessel System"),
        Blocks(
            Paragraph(Text("Definition of Bessel systems: band limits, Schur bounds, tail bound; the constants of the open-cell bound, which is proved in New.RealPlace.OpenCellBound.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/BesselSystem.BesselSystem"),
                H("BesselSystem"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A full and a cut Bessel function on G₁ for an irreducible rep, with IsCutPair, Schur bounds |I|/deg for derivatives (HasSchurBound), 8·rank ≤ b, and band limits HasBandLimits."))),
                DescribeRole.Definition))));
}
