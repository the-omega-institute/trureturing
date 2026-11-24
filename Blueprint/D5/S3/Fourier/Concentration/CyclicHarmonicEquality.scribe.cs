using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CyclicHarmonicEqualityDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CyclicHarmonicEquality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "When the second Fourier mode vanishes, saturation of the first requires a quarter turn.",
        H("Equality for the First Two Cyclic Fourier Modes"),
        Blocks(
            Paragraph(Text(
                "Let q be a positive integer and let w be a nonnegative real weight of total mass "
                + "one on ZMod q. Use the unnormalized discrete Fourier transform and write c for "
                + "the squared magnitude at frequency one. Assume the coefficient at frequency two "
                + "vanishes. Write ord for additive order.")),
            Describe.Lean(
                DescribeId.Create("first-mode-equality"),
                DeclarationHandle.Create(Owner + ".zmod_first_mode_le_half_of_second_zero"),
                H("The upper bound and all its equality cases"),
                StatementSource.FromAuthor(Classification()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let m be the first coefficient and z(j) be the unit character at residue j. "
                    + "The w-weighted variance of the real part of the projection by the conjugate "
                    + "of m is c/2 minus c squared. At equality each positive mass has projected "
                    + "real part 1/2. Its projected imaginary part is then either 1/2 or −1/2. "
                    + "The imaginary mean vanishes, so both points occur with equal weights. "
                    + "Injectivity of the cyclic character gives exactly two residues, and the "
                    + "two phases differ by a quarter turn. Conversely, the first coefficient of "
                    + "the equal two-point law is the average of two perpendicular unit phases."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the same positive modulus q, write E(q) for existence of a nonnegative "
                + "weight of total mass one with second coefficient zero and squared first "
                + "magnitude one half.")),
            Describe.Lean(
                DescribeId.Create("first-mode-attainment"),
                DeclarationHandle.Create(Owner + ".zmod_exists_first_mode_half_of_second_zero"),
                H("Exactly the moduli that admit equality"),
                StatementSource.FromAuthor(Disp(Seq(Call("E", F.Id("q")), Sp, Iff, Sp,
                    D(4), Sp, Mid, Sp, F.Id("q")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The additive order of the difference divides q. When four divides q, "
                    + "choose the residues zero and q/4. The two second-mode phases cancel, "
                    + "and the classification gives equality."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For an indexed lattice spectrum a(j) with normalized weights w(j), fix a "
                + "frequency k modulo q. Send index j to the residue b(j)=a(j)k and sum its "
                + "weight into the mass v at that residue. The same pushed-forward probability "
                + "weight v supplies both modes. Expanding the sums by fibers recovers mode k "
                + "of the original spectrum at mode one of v, and mode 2k at mode two of v. "
                + "The classification then bounds the squared magnitude at k when the coefficient "
                + "at 2k is zero. A quantitative bound for the high-order weighted collisions of "
                + "actual zeta ordinates at positive resolution remains open.")))));

    private static Formula Classification()
    {
        var q = F.Id("q");
        var c = F.Id("c");
        var a = F.Id("a");
        var b = F.Id("b");
        var j = F.Id("j");
        var half = new Formula.Fraction(D(1), D(2));
        var group = Call("ZMod", q);
        var outside = Seq(j, Sp, Neq, Sp, a, Sp, Land, Sp, j, Sp, Neq, Sp, b);
        var zeroElsewhere = Seq(Open, Forall, Sp, j, Sp, InMacro, Sp, group, Comma, Sp,
            outside, Sp, Implies, Sp, Call("w", j), Sp, Eq, Sp, D(0), Close);
        var support = Seq(Exists, Sp, a, Comma, Sp, b, Sp, InMacro, Sp, group, Comma, Sp,
            a, Sp, Neq, Sp, b, Sp, Land, Sp, Call("ord", Seq(b, Minus, a)), Sp, Eq, Sp, D(4),
            Sp, Land, Sp, Call("w", a), Sp, Eq, Sp, half, Sp, Land, Sp, Call("w", b), Sp, Eq, Sp,
            half, Sp, Land, Sp, zeroElsewhere);
        return Disp(Seq(c, Sp, Leq, Sp, half, Sp, Land, Sp, Open, c, Sp, Eq, Sp, half,
            Sp, Iff, Sp, support, Close));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
