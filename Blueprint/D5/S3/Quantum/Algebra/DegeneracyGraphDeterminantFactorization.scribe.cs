using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class DegeneracyGraphDeterminantFactorizationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Algebra/DegeneracyGraphDeterminantFactorization";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/kempramgoolam2026degeneracy");
    private static DocumentBlock.Describe Declaration(int number, string name) =>
        Describe.Lean(DescribeId.Create($"declaration-{number:00}"), DeclarationHandle.Create($"{Module}.{name}"), H(name), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("This declaration is part of the final signed source factorization. It preserves literal ordered sibling pairs, actual SourcePairTailWitness cardinalities, and the explicit integer sign."))), name == "sourceSquare_det_factorization" ? DescribeRole.Theorem : DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full arbitrary-depth determinant is the signed literal sibling-difference product with source witness multiplicities.",
        H("Degeneracy Graph Determinant: Factorization"),
        Blocks(
            Paragraph(Text("SourceSiblingPair separates only ordered siblings under one parent. sourceExponent is the actual cardinality of SourcePairTailWitness, so all exponents are positive where the source requires them and the bottom exponent is one. sourceFactorProduct is the literal product over every level and sibling pair; sourceSquare_det_factorization combines the recurrence with the exact row/column enumeration sign and no unproved evaluation-equivalence proxy.")),
            Paragraph(Text("This owner is the canonical Lean resolution of the source determinant clauses (6.22)–(6.27), conditional only on the SourceTree sibling-injectivity hypothesis already present in the formal statement.")),
            Declaration(1, "SourceSiblingPair"), Declaration(2, "sourceExponent"), Declaration(3, "sourceFactorProduct"), Declaration(4, "sourceSquare_det_factorization"))));
}
