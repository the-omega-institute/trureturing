using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Eigenstructure;

internal sealed class GoldenFiberCoordinatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two golden fiber coordinates have exact Beatty floor formulas.",
        H("Exact Beatty Formulas for Golden Fiber Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-fiber-coordinates-have-exact-beatty-formulas"),
                DeclarationHandle.Create(
                    "D5/S1/Eigenstructure/GoldenFiberCoordinates.golden_fiber_coordinates"),
                H("The golden fiber coordinates are Beatty floor differences"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("v"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
                    Comma, Esc, D(1), Sp, Leq, Sp, F.Id("v"), Sp, Implies, Sp,
                    F.Id("a"), Open, F.Id("v"), Close, Eq,
                    Lfloor, Frac, Grp(F.Id("v"), Plus, D(1)), Grp(Varphi), Rfloor,
                    Minus,
                    Lfloor, Frac, Grp(F.Id("v"), Plus, D(1)),
                    Grp(Varphi, Caret, Grp(D(2))), Rfloor,
                    Comma, Quad, Sp,
                    F.Id("b"), Open, F.Id("v"), Close, Eq,
                    Lfloor, Frac, Grp(F.Id("v"), Plus, D(1)),
                    Grp(Varphi, Caret, Grp(D(2))), Rfloor,
                    Comma, Quad, Sp,
                    F.Id("a"), Open, F.Id("v"), Close, Plus,
                    F.Id("b"), Open, F.Id("v"), Close, Eq,
                    Lfloor, Frac, Grp(F.Id("v"), Plus, D(1)), Grp(Varphi), Rfloor,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The source coordinates are defined from the Zeckendorf displacement reading "
                        + "by a(v) = 2 S(v) - 3 v and b(v) = 2 v - S(v). For every positive "
                        + "index, both coordinates and their sum are identified with exact floor "
                        + "readings at the inverse golden ratio and its square.")),
                    Paragraph(Text(
                        "The proof reuses the repository's frozen displacement identity "
                        + "S(v) = floor((v + 1) phi) - 1. Pinned Mathlib supplies the golden-ratio "
                        + "identities, irrationality under nonzero natural scaling, and floor interval "
                        + "bounds. No pinned declaration states the assembled coordinate triple.")),
                    Paragraph(Text(
                        "This deposit closes only theorem 6.48-prime, clause 2. It does not claim the "
                        + "fiber criterion, capacity statement, support interval, or first-index formula "
                        + "from the surrounding source entries."))),
                DescribeRole.Theorem)),
        []));
}
