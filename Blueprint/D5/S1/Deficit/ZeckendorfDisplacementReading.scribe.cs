using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit;

internal sealed class ZeckendorfDisplacementReadingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Zeckendorf up-shift displacement decode equals the shifted golden Beatty reading.",
        H("The Zeckendorf Up-Shift Displacement Decode Is a Golden Beatty Reading"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zeckendorf-displacement-reading"),
                DeclarationHandle.Create(
                    "D5/S1/Deficit/ZeckendorfDisplacementReading.displacement_decode_eq_beatty_floor"),
                H("The up-shift displacement decode equals floor((v+1) phi) minus one"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("S"), Open, F.Id("v"), Close, Sp, Eq, Sp,
                    Lfloor, Sp, Open, F.Id("v"), Plus, D(1), Close, Cdot, Varphi, Sp, Rfloor, Sp,
                    Minus, Sp, D(1)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Zeckendorf up-shift displacement decode of v is S(v) = sum over the occupied "
                        + "Fibonacci indices k of the canonical Zeckendorf digits of v of F_{k+1} — each index "
                        + "k is shifted up to k+1 (the up-shift of slope phi, not the down-slope 1/phi). The "
                        + "identity is S(v) = floor((v+1) * phi) - 1 for every v; for instance S(0..6) = "
                        + "0, 2, 3, 5, 7, 8, 10, matching floor((v+1) phi) - 1 including the boundary v = 0.")),
                    Paragraph(Text(
                        "Aggregate Binet, F_{k+1} = phi * F_k + psi^k summed over the digit list, reduces the "
                        + "real value of S(v) to v * phi + sum_k psi^k. On a canonical Zeckendorf digit list "
                        + "(gaps at least 2, indices at least 2) the conjugate tail sum_k psi^k lies strictly in "
                        + "the interval (-1/phi^2, 1/phi), so S(v) is the unique integer in "
                        + "(v*phi - 1/phi^2, v*phi + 1/phi); Int.floor_eq_iff with phi - 1 = 1/phi closes the "
                        + "closed form.")),
                    Paragraph(Text(
                        "Only the up-shift displacement reading identity S(v) = floor((v+1) phi) - 1 is recorded. "
                        + "The deficit forms beta'(v) = S(v) - v*phi and beta(v) = S(v) - v*psi, and the "
                        + "downstream length recovery ell = log n, are not covered by this statement."))),
                DescribeRole.Theorem))));
}
