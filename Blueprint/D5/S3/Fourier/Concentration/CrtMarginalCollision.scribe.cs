using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CrtMarginalCollisionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CrtMarginalCollision";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Separate collision statistics leave the mixed character contribution undetermined.",
        H("Joint collision mass from two cyclic marginals"),
        Blocks(
            Paragraph(Text(
                "On the residues modulo six let P give masses 1/2, 1/4, 1/4 at 0, 3, 4. "
                + "Let Q give masses 3/4 and 1/4 at 0 and 1. All other masses vanish in each law. "
                + "For each positive integer p, write E(P) and E(Q) for the collision masses "
                + "of two independent p-fold sums modulo six. Write A and B for the collision "
                + "masses for P modulo two and three, and C and F for those for Q.")),
            Describe.Lean(
                DescribeId.Create("crt-marginal-collision-gap"),
                DeclarationHandle.Create(Owner + ".crt_marginal_collision_gap"),
                H("Identical marginal collision profiles with opposite factorization errors"),
                StatementSource.FromAuthor(Bounds()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two weights induce the same law modulo two and the same law modulo "
                    + "three. Use the exact cyclic character average "),
                    Ref("D5/S3/Fourier/Concentration/CyclicCollisionCertificate.cyclicCollisionMass_fourier"),
                    Text(" to evaluate the collision mass of the degree-p sums. The squared "
                        + "mixed Fourier magnitudes of P and Q are 1/16 and 13/16. The product "
                        + "of the two pure squared magnitudes is 7/64. Each mixed contribution "
                        + "occurs twice among the six characters. The difference from A B is "
                        + "therefore controlled by these distinct pth powers. This comparison "
                        + "treats a fixed finite modular law. The weighted near-collision "
                        + "estimate for actual zeta ordinates remains open."))),
                DescribeRole.Theorem))));

    private static Formula Bounds()
    {
        var p = F.Id("p");
        var left = F.Id("A");
        var right = F.Id("B");
        var product = Multiply(left, right);
        var ep = Call("E", F.Id("P"));
        var eq = Call("E", F.Id("Q"));
        var common = new Formula.Power(new Formula.Fraction(D(7), D(6, 4)), p);
        Formula Gap(Formula value) => new Formula.Fraction(
            Seq(new Formula.Power(new Formula.Fraction(value, D(1, 6)), p), Minus, common), D(3));
        return Disp(Seq(left, Eq, F.Id("C"), Sp, Land, Sp,
            right, Eq, F.Id("F"), Sp, Land, Sp,
            ep, Lt, product, Lt, eq, Sp, Land, Sp,
            Seq(ep, Minus, product, Eq, Gap(D(1))), Sp, Land, Sp,
            Seq(eq, Minus, product, Eq, Gap(D(1, 3)))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
