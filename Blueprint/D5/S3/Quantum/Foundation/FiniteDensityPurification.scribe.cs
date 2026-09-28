using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;
internal sealed class FiniteDensityPurificationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite density state has a canonical normalized purification with exact reduced marginal.",
        H("Finite Density Purification"), Blocks(Describe.Lean(
            DescribeId.Create("finite-density-purification"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteDensityPurification.purify_spec"),
            H("Canonical purification has the exact marginal"),
            StatementSource.FromAuthor(Disp(Seq(Operatorname, Grp(F.Id("traceRight")), Open, Operatorname, Grp(F.Id("pure")), Open, Operatorname, Grp(F.Id("purify")), Open, F.Id("rho"), Close, Close, Close, Eq, F.Id("rho"), Dot))),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Quantum/braunsteinpati2007nohiding")), Blocks(
                Paragraph(Text("For a finite density state ρ on d, purify constructs the canonical ket on d × d from the spectral data of ρ; pure forms its rank-one state and tracing out the purifying factor returns exactly ρ.")),
                Paragraph(Text("The ket is normalized by the finite spectral decomposition, and the source retains Fintype and DecidableEq assumptions where required. This records the exact marginal identity only; it does not add a new Lean wrapper.")),
                Paragraph(Text("The declaration is reused from the selected upstream Physlib provenance at immutable revision 6a09b2d1761a0d4430083045a247eb121d8da260."))),
            DescribeRole.Theorem))));
}
