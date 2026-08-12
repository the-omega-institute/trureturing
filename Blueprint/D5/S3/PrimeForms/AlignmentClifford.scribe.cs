using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class AlignmentCliffordDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every matrix on the alignment hyperplane sandwiches K to a determinant-scaled copy of K.",
        H("The Generalized-Flow Identity of the Alignment Matrix"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("alignment-matrix-generalized-flow-identity"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/AlignmentClifford.generalized_flow"),
                H("Generalized-flow identity on the alignment hyperplane"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("K"), Sp, Eq, Sp,
                    Begin, Grp(F.Id("pmatrix")),
                    D(1), Amp, Minus, D(2), RowBreak, D(2), Amp, Minus, D(1),
                    End, Grp(F.Id("pmatrix")), Comma, Sp,
                    F.Id("K"), Caret, D(2), Sp, Eq, Sp, Minus, D(3), Sp, F.Id("I"), Comma, RowBreak,
                    Forall, Sp, Beta, Sp, InMacro, Sp, F.Id("V"), Comma, Sp,
                    Beta, Sp, F.Id("K"), Sp, Beta, Sp, Eq, Sp,
                    Open, Operatorname, Grp(F.Id("det")), Sp, Beta, Close, Sp, F.Id("K")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The alignment matrix K = [[1,-2],[2,-1]] is an integer 2x2 matrix that squares "
                        + "to -3 times the identity, so it behaves as a square root of -3. Its alignment "
                        + "hyperplane is V = { X : tr(X K) = 0 }, the integer matrices X whose trace "
                        + "against K vanishes.")),
                    Paragraph(Text(
                        "The generalized-flow identity states that every matrix on this hyperplane rescales "
                        + "K by its determinant: for all beta in V, beta K beta = (det beta) K. The "
                        + "identity holds for every beta on the hyperplane, with no unimodularity "
                        + "assumption; the unimodular case det beta = +-1, where beta sends K to +-K, is a "
                        + "special case. Moreover the hyperplane is closed under the sandwich map: if beta "
                        + "and gamma lie in V then so does beta gamma beta.")),
                    Paragraph(Text(
                        "The flow identity is proved by reading off the single hyperplane constraint and "
                        + "applying it to each of the four entries of beta K beta - (det beta) K; closure "
                        + "is a trace-cyclicity corollary. Only these three clauses — the square identity, "
                        + "the generalized flow, and closure — are recorded here. The unimodular acts-by-"
                        + "plus-or-minus-one reading, the flow / self-insertion / even-texture unification, "
                        + "the paired-and-zero census certificate, and the phase-charge parity "
                        + "interpretation of the wider result are not covered by this statement."))),
                DescribeRole.Theorem))));
}
