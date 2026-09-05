using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Asymptotics.Interference;

internal sealed class BraggZeroFreeDiskDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive Bragg peak and its Bernstein variation bound determine a sharp zero-free disk.",
        H("Sharp Bragg Zero-Free Disk"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bragg-peak-has-a-sharp-zero-free-disk"),
                DeclarationHandle.Create(
                    "D5/S0/Asymptotics/Interference/BraggZeroFreeDisk.bragg_zero_free_disk"),
                H("The finite Bragg radius is zero-free and sharp"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let c denote the positive magnitude of the relevant Fourier-Bohr "
                            + "coefficient. The peak lower bound is T c, while the Bernstein "
                            + "estimate supplies Lipschitz constant L = e T (phi T + 2). "
                            + "Their quotient is the exact finite radius r = c/(e(phi T + 2)).")),
                    Paragraph(Text(
                        "Inside the open disk, the maximum possible variation from the center "
                            + "is strictly smaller than T c. The reverse triangle inequality "
                            + "therefore prevents the function from vanishing there.")),
                    Paragraph(Text(
                        "The linear profile Q(w) = T c - L w has the same central height and "
                            + "exact Lipschitz constant, and it vanishes at distance r. This "
                            + "boundary witness shows that the strict disk cannot be enlarged "
                            + "uniformly from only the two quantitative hypotheses.")),
                    Paragraph(Text(
                        "The source's c/(e phi T)(1+o(1)) is an asymptotic rewrite. This theorem "
                            + "retains the finite +2 term and explicitly assumes T, phi, and c "
                            + "positive, excluding totalized-division degeneracies."))),
                DescribeRole.Theorem))));

    private static Formula Absolute(Formula value) => new Formula.Absolute(value);

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula p = F.Id("P");
        Formula q = F.Id("Q");
        Formula z0 = new Formula.Subscript(F.Id("z"), D(0));
        Formula w = F.Id("w");
        Formula boundary = new Formula.Subscript(F.Id("w"), Star);
        Formula t = F.Id("T");
        Formula phi = Varphi;
        Formula coefficient = F.Id("c");
        Formula scale = Add(Multiply(phi, t), D(2));
        Formula denominator = Multiply(F.Id("e"), scale);
        Formula radius = new Formula.Fraction(coefficient, denominator);
        Formula lipschitz = Multiply(Multiply(F.Id("e"), t), scale);
        Formula ball = Call("B", z0, radius);
        Formula pAt(Formula point) => Call("P", point);
        Formula qAt(Formula point) => Call("Q", point);
        Formula zeroFree = Seq(
            Forall, Sp, w, InMacro, complex, Comma, Sp,
            Absolute(Subtract(w, z0)), Sp, Lt, Sp, radius, Sp, Rightarrow, Sp,
            pAt(w), Sp, Neq, Sp, D(0));
        Formula sharpWitness = Seq(
            Exists, Sp, q, Colon, Sp, new Formula.TypeArrow(complex, complex), Comma, Sp,
            Exists, Sp, boundary, InMacro, complex, Comma, Sp,
            Absolute(qAt(D(0))), Sp, Eq, Sp, Multiply(t, coefficient), Sp, Land, Sp,
            Open, Forall, Sp, w, InMacro, complex, Comma, Sp,
            Absolute(Subtract(qAt(w), qAt(D(0)))), Sp, Eq, Sp,
            Multiply(lipschitz, Absolute(w)), Close, Sp, Land, RowBreak, Grp(),
            Absolute(boundary), Sp, Eq, Sp, radius, Sp, Land, Sp,
            qAt(boundary), Sp, Eq, Sp, D(0));

        return Disp(Seq(
            Forall, Sp, p, Colon, Sp, new Formula.TypeArrow(complex, complex), Comma, Sp,
            z0, InMacro, complex, Comma, Sp,
            t, Comma, Sp, phi, Comma, Sp, coefficient, InMacro, real, Comma, RowBreak, Grp(),
            t, Gt, D(0), Comma, Sp, phi, Gt, D(0), Comma, Sp, coefficient, Gt, D(0), Comma, Esc,
            Absolute(pAt(z0)), Sp, Geq, Sp, Multiply(t, coefficient), Comma, RowBreak, Grp(),
            Open, Forall, Sp, w, InMacro, complex, Comma, Sp,
            Absolute(Subtract(pAt(w), pAt(z0))), Sp, Leq, Sp,
            Multiply(lipschitz, Absolute(Subtract(w, z0))), Close, RowBreak, Grp(),
            Rightarrow, Sp, Open, Open, zeroFree, Close, Sp, Land, Sp,
            z0, InMacro, ball, Sp, Land, Sp,
            pAt(z0), Sp, Neq, Sp, D(0), Close, Sp, Land, RowBreak, Grp(),
            sharpWitness, Dot));
    }
}
