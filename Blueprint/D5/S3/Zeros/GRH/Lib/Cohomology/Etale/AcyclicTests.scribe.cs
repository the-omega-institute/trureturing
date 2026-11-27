using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class AcyclicTestsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Acyclic Tests", H("Acyclic Tests"),
        Blocks(
            Paragraph(Text("Relatively representable (affine) maps of functors on rings: pullbacks, closed and open loci. Tests are acyclic; tests and locally constant functions commute with filtered colimits.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/AcyclicTests.continuousUpTo_locConstCoeff"),
                H("continuousUpTo_locConstCoeff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If a test ring A is the filtered colimit, as a ring, of test rings A_j, then the Λ-cohomology H^n(h_A) on test rings is the colimit of the H^n(h_{A_j}), for every n.")))))));
}
