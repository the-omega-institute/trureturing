using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.Sigma;

internal sealed class SigmaFunctionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sigma Function", H("Sigma Function"),
        Blocks(
            Paragraph(Text("From degree two on, theta functions have no common zero. Sigma function as odd canonical theta function; zeros, dimension, addition formula.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/Sigma/SigmaFunction.sigma_add_mul_sigma_sub"),
                H("sigma_add_mul_sigma_sub"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Addition formula for the sigma function of L: for u and v outside the lattice, σ(u + v)·σ(u − v) = (℘(v) − ℘(u))·σ(u)²·σ(v)².")))))));
}
