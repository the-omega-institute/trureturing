using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class GoldenModularStandardPairDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The golden Fibonacci matrix yields an explicit finite-dimensional modular standard pair.",
        H("Golden Modular Standard Pair"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-finite-dimensional-modular-standard-pair"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Matrix/GoldenModularStandardPair.golden_modular_standard_pair"),
                H("The golden finite-dimensional modular standard pair"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("F"), Caret, Grp(D(2)), Eq,
                    F.Id("Delta"), Eq, Begin, Grp(F.Id("pmatrix")),
                    D(1), Amp, D(1), RowBreak, D(1), Amp, D(2),
                    End, Grp(F.Id("pmatrix")), Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Spec")), Open, F.Id("Delta"), Close, Eq,
                    OpenBrace, F.Id("phi"), Caret, Grp(D(2)), Comma,
                    F.Id("phi"), Caret, Grp(Seq(Minus, D(2))), CloseBrace, Sp, Land, Sp,
                    F.Id("J"), F.Id("Delta"), F.Id("J"), Eq,
                    F.Id("Delta"), Caret, Grp(Minus, D(1)), Sp, Land, Sp,
                    F.Id("S"), Eq, F.Id("J"), Sqrt, Grp(F.Id("Delta")), Sp, Land, Sp,
                    F.Id("S"), Caret, Grp(D(2)), Eq, F.Id("I"), Sp, Land, Sp,
                    F.Id("H"), Underscore, Grp(Seq(F.Id("phi"), Comma, F.Id("R"))), Eq,
                    OpenBrace, F.Id("psi"), Colon, F.Id("S"), F.Id("psi"), Eq,
                    F.Id("psi"), CloseBrace, Sp, Land, Sp,
                    F.Id("K"), Eq, Operatorname, Grp(F.Id("log")), Open,
                    F.Id("Delta"), Close, Sp, Land, Sp,
                    Operatorname, Grp(F.Id("Spec")), Open, F.Id("K"), Close, Eq,
                    OpenBrace, D(2), F.Id("log"), F.Id("phi"), Comma,
                    Minus, D(2), F.Id("log"), F.Id("phi"), CloseBrace))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the displayed two-dimensional Fibonacci matrix, its square is " +
                        "the positive matrix with rows (1,1) and (1,2), and its complete real " +
                        "point spectrum is the reciprocal pair phi squared and phi to the " +
                        "minus two. In the corresponding eigenbasis, swapping the two " +
                        "coordinates and complex-conjugating is an antilinear isometry J. " +
                        "It conjugates Delta to its inverse. The explicitly positive square " +
                        "root gives an involutive Tomita map S, whose fixed vectors form the " +
                        "stated real fixed space. Coordinatewise logarithm gives the modular " +
                        "Hamiltonian with the complete two-point spectrum plus or minus twice " +
                        "log phi."))),
                DescribeRole.Theorem))));
}
