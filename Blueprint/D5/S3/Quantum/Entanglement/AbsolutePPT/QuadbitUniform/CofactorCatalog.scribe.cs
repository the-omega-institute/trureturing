using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class CofactorCatalogDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer oriented support checker.",
        H("Integer oriented support checker"), Blocks(
            Describe.Lean(DescribeId.Create("appt-quadbit-cofactorcatalog"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/CofactorCatalog.CaseValid"),
                H("Integer oriented support checker"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The integer matrix aZ contains the three boundary rows. Appending minus the three by three " +
                    "identity gives bZ with nineteen columns; its real cast is the slack kernel matrix. Each " +
                    "original gap vector is aligned with its ray label and its three exact slacks. For an " +
                    "increasing four-column support, CaseValid checks one of three alternatives: opposite " +
                    "cofactor signs, all cofactors zero, or an explicitly oriented zero extension equal to a " +
                    "strictly positive integer multiple of one original catalog vector. The witness is " +
                    "supplied, rather than searched over the catalog."))), DescribeRole.Definition),
            Paragraph(Text("These statements concern real scalar spectra and finite cofactor certificates. Connecting " +
                    "the boundary inequalities to a physical APPT model, constructing an attaining state, and " +
                    "determining a purity supremum require additional results.")))));
}
