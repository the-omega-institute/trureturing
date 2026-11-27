using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.DiscreteSeries.FlenstedJensen;

internal sealed class RepresentationDefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Representation Defs", H("Representation Defs"),
        Blocks(
            Paragraph(Text("Parameters, lowest K-type, Flensted-Jensen integral, coefficient, degree and kernel for U(p,q). Holomorphic functions of weight u on G·B, highest coefficient, dominance, torus. gl_n-modules, unitarisable Banach representations, derivatives, K-highest vectors, Casimir elements, root cone.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/DiscreteSeries/FlenstedJensen/RepresentationDefs.casimir"),
                H("casimir"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For a relation r on indices, the endomorphism Σ E_ab E_ba of a gl_n-module, summed over the pairs (a,b) with r(a,b).")))))));
}
