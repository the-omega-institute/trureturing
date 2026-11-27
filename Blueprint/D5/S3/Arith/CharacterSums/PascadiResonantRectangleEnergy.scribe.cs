using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.CharacterSums;

internal sealed class PascadiResonantRectangleEnergyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CharacterSums/PascadiResonantRectangleEnergy.";
    private static Formula P => F.Id("p");
    private static Formula Q => F.Id("q");
    private static Formula A => F.Id("A");
    private static Formula R => F.Id("R");
    private static Formula C => F.Id("c");
    private static Formula U => F.Id("u");
    private static Formula Frequency => F.Id("f");
    private static Formula Energy => Call("E", R, C);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete normalized dual energy on a literal resonant rectangle is bounded by nine times the prime times the square of its side bound.",
        H("Complete dual energy on a literal resonant rectangle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pascadi-normalized-rectangle-energy"),
                DeclarationHandle.Create(Prefix + "normalizedRectangleEnergy"),
                H("The full prime-square frequency average"),
                StatementSource.FromAuthor(EnergyDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let p be prime, q = p², and fix the literal integer pivot set in R. A pivot (a,b) maps to u = ((rho a + sigma b)/p, (s a − r b)/p) reduced modulo q. The equation r rho + s sigma = p and the literal resonance make the divisions exact. S(R) is the resulting reduced pivot set.")),
                    Paragraph(Text("K is the full dual character kernel with the common mask chi. Its fibre consists of all points (x,y) for which a, b, x, y, h−x−y, x+y, h−x and h−y are units modulo q and g a b x y (h−x−y) = h modulo q. The complete sum runs over two independent two-coordinate frequencies, so its denominator is q⁴."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pascadi-complete-resonant-rectangle-energy"),
                DeclarationHandle.Create(Prefix + "complete_resonant_rectangle_energy_le"),
                H("A uniform complete-energy bound"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, R, Comma, Sp, C, Comma, Sp, Call("CoefficientBound", R, C),
                    Sp, Implies, Sp, Energy, Le, D(9), Sp, P, Sp, A, Caret, D(2)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("R fixes a prime p > 3, an integer p ≤ A < p², a primitive pair (r,s), and integers rho and sigma with r rho + s sigma = p. The literal pivots have unit coordinates and lie in the closed rectangle [L,L+A] × [M,M+A]; each satisfies p divides s a − r b. The parameters g,h are modulo q and g is a unit. Both the common mask and the tested coefficients have modulus at most one at each retained pivot.")),
                    Paragraph(Text("Reduction is injective on these literal coordinates. At most two lower roots occur for each first coordinate. A smooth lower root allows at most p lifts, because the free upper digit determines the other, and the only possible singular lower root has at most p² lifts. Thus each fibre has at most 3p² points. The resonant box contains at most 3A²/p distinct pivots, including both endpoints. The exact complete energy identity now gives the bound.")),
                    Paragraph(Text("The result is about the complete frequency sum, not a weighted RMS or a normalized concentration bound on a short window."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula EnergyDefinition() => Disp(Seq(
        Energy, Eq, Frac,
        Grp(Sum, Underscore, Grp(Frequency, InMacro, Sp, Call("DualFrequency", Q)), Sp,
            Lvert, Sum, Underscore, Grp(U, InMacro, Sp, Call("S", R)), Sp,
            Call("c", U), Sp, Call("K", U, Frequency), Rvert, Caret, D(2)),
        Grp(Q, Caret, D(4))));
}
