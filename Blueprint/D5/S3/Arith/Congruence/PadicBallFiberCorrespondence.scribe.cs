using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class PadicBallFiberCorrespondenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A prime-power congruence class is the integer trace of a p-adic closed ball.",
        H("Prime-Power Congruence Fibers as P-Adic Balls"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-power-congruence-is-p-adic-proximity"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/PadicBallFiberCorrespondence."
                        + "modeq_iff_padic_dist_le"),
                H("Prime-power congruence is exactly p-adic proximity"),
                StatementSource.FromAuthor(ModEqPadicDistanceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a prime p and a precision k, two integers occupy the same residue "
                            + "class modulo p^k exactly when their images in the p-adic numbers "
                            + "are at distance at most p^(-k). Thus arithmetic agreement through "
                            + "k p-adic digits is the same condition as metric proximity at the "
                            + "corresponding scale.")),
                    Paragraph(Text(
                        "The distance between the embedded integers is the p-adic norm of their "
                            + "difference. Divisibility of that difference by p^k is equivalent "
                            + "to its norm being bounded by p^(-k), which converts the congruence "
                            + "condition into the stated distance bound in both directions."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("congruence-fiber-is-closed-ball-intersected-with-integers"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/PadicBallFiberCorrespondence."
                        + "congruenceFiber_eq_closedBall_inter_range"),
                H("A congruence fiber is the integer trace of a closed ball"),
                StatementSource.FromAuthor(CongruenceFiberFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a prime p, precision k, and integer center x, the p-adic images of "
                            + "integers congruent to x modulo p^k are precisely the points in the "
                            + "closed ball of radius p^(-k) around x that also lie in the embedded "
                            + "copy of the integers. The integer-image restriction is essential: "
                            + "the ambient p-adic ball contains points that do not arise from integers.")),
                    Paragraph(Text(
                        "Membership in the congruence fiber supplies an integer representative y. "
                            + "The distance characterization turns x congruent to y modulo p^k into "
                            + "the closed-ball inequality, while the embedding of y supplies membership "
                            + "in the integer image. Conversely, an integer point of the ball has a "
                            + "representative y, and the same characterization recovers its congruence "
                            + "to x, giving both inclusions of the set equality."))),
                DescribeRole.Theorem))));

    private static Formula ModEqPadicDistanceFormula()
    {
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula modulus = Seq(p, Caret, Grp(k));
        Formula radius = Seq(p, Caret, Grp(Minus, k));
        Formula distance = Seq(
            new Formula.Subscript(F.Id("d"), p), Open, x, Comma, Sp, y, Close);

        return Disp(Seq(
            Forall, Sp, p, Comma, Sp, k, Sp, InMacro, Sp, naturals, Comma, Sp,
            p, Sp, F.Text, Grp(Sp, F.Id("prime")), Comma, Sp,
            x, Comma, Sp, y, Sp, InMacro, Sp, integers, Comma, Esc,
            x, Sp, Equiv, Sp, y, Sp, Open,
            Operatorname, Grp(F.Id("mod")), Sp, modulus, Close, Sp,
            Iff, Sp, distance, Sp, Leq, Sp, radius, Dot));
    }

    private static Formula CongruenceFiberFormula()
    {
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula x = F.Id("x");
        Formula z = F.Id("z");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula padics = Seq(Mathbb, Grp(F.Id("Q")), Underscore, Grp(p));
        Formula radius = Seq(p, Caret, Grp(Minus, k));
        Formula distance = Seq(
            new Formula.Subscript(F.Id("d"), p), Open, x, Comma, Sp, z, Close);
        Formula embeddedIntegers = Seq(
            new Formula.Subscript(F.Id("iota"), p), Open, integers, Close);

        return Disp(Seq(
            Forall, Sp, p, Comma, Sp, k, Sp, InMacro, Sp, naturals, Comma, Sp,
            p, Sp, F.Text, Grp(Sp, F.Id("prime")), Comma, Sp,
            x, Sp, InMacro, Sp, integers, Comma, Esc,
            Call("congruenceFiber", p, k, x), Sp, Eq, Sp,
            OpenBrace, Sp, z, Sp, InMacro, Sp, padics, Sp, Mid, Sp,
            distance, Sp, Leq, Sp, radius, Sp, Land, Sp,
            z, Sp, InMacro, Sp, embeddedIntegers, Sp, CloseBrace, Dot));
    }
}
