using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Resolvent;

internal sealed class ActualXiTaylorDictionaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual xi Taylor coefficients are folded moments.",
        H("Actual xi Taylor coefficients are folded moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actualxitaylordictionary"),
                DeclarationHandle.Create("D5/S3/Zeros/Resolvent/ActualXiTaylorDictionary.actual_xi_taylor_moment"),
                H("Actual xi Taylor coefficients are folded moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The complex moment of order j is the complete sum of weight times node to power j over actual positive-height zero indices. Absolute weight summability and the bounded complex nodes justify every moment and the double geometric series. Its sum on norm(w) less than one quarter is the independently defined xiOdd(w).")),
                    Paragraph(Text("The full scalar formal power series has zero even coefficients and moment j at coefficient 2j+1. The kernel-checked formal-power-series factorial identity identifies moment j with iteratedDeriv(2j+1, xiOdd)(0) divided by (2j+1) factorial, at every natural j. All even iterated derivatives vanish. The same full series proves analyticity throughout the disk. Conjugation of actual indices makes every moment real.")),
                    Paragraph(Text("Let W be the complete sum of absolute weights and Lambda the supremum of the node norms with zero included. Lambda lies between zero and one. The moment norm is at most W times Lambda to power j. The coefficients are analytic data of the genuine xi expression; the moment interpretation is a proved identity, not a replacement definition of xi or its logarithmic derivative.")))))));
}
