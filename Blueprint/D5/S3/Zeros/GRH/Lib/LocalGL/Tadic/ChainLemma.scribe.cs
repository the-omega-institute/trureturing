using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.Tadic;

internal sealed class ChainLemmaDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chain Lemma", H("Chain Lemma"),
        Blocks(
            Paragraph(Text("An unramified exponent with sorted roots is non-zero on spherical vectors. Chain lemma: spherical vector orthogonal to a polynomial in U; strings of Satake roots.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/Tadic/ChainLemma.isRoot_string_of_norm"),
                H("isRoot_string_of_norm"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let x ≠ 0 be a spherical Hecke eigenvector in a smooth unitary representation of GL_N(E_w), with Hecke polynomial P. If P(c) = 0 and |c|² q^k = q^N, then c, cq, …, cq^(k−1) are all roots of P.")))))));
}
