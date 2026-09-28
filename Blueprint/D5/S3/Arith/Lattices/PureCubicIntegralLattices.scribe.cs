using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class PureCubicIntegralLatticesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two integral rational bases in a pure cubic field have explicit lattice discriminants.",
        H("Integral Lattices in a Pure Cubic Field"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pure-cubic-integral-lattices"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Lattices/PureCubicIntegralLattices.integral_cubic_lattices"),
                H("Two integral rational bases and their trace discriminants"),
                StatementSource.FromAuthor(LatticeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K be a characteristic-zero field with a rational power basis "
                            + "(1, alpha, alpha squared) of dimension three. Assume "
                            + "alpha cubed equals m times n squared, where m and n are nonzero "
                            + "integers. Let c, a, k, and v be integers with v equal to one or "
                            + "minus one, c cubed times m times n squared equal to one plus "
                            + "nine a, and c squared times n equal to v plus three k. Define "
                            + "beta and gamma as displayed.")),
                    Paragraph(Text(
                        "The cubic equations for alpha and beta make them integral. For "
                            + "t=c alpha, the element (1+t+t squared)/3 satisfies the monic "
                            + "polynomial T cubed minus T squared minus 3aT minus 3a squared. "
                            + "It is integral, and gamma differs from it by the integral "
                            + "multiple k beta.")),
                    Paragraph(Text(
                        "The rational power basis has discriminant minus 27 times "
                            + "(m n squared) squared. The two displayed changes of basis "
                            + "have determinants 1/n and v/(3n). Their nonzero discriminants "
                            + "also establish that both triples are rational bases. These are "
                            + "discriminants of the specified integral lattices. The rational "
                            + "power basis is assumed here; the theorem does not construct it "
                            + "from irreducibility, identify the field discriminant, or prove "
                            + "maximality."))),
                DescribeRole.Theorem))));

    private static Formula LatticeFormula()
    {
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula gamma = F.Id("gamma");
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula c = F.Id("c");
        Formula v = F.Id("v");
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula rational = Seq(Mathbb, Grp(F.Id("Q")));
        Formula mn = Seq(m, n);
        Formula basisOne = Call("Basis", rational, D(1), alpha, beta);
        Formula basisTwo = Call("Basis", rational, D(1), alpha, gamma);
        Formula discrOne = Call("discr", rational, D(1), alpha, beta);
        Formula discrTwo = Call("discr", rational, D(1), alpha, gamma);

        return Disp(new Formula.Aligned([
            Seq(beta, Sp, Eq, Sp, Frac, Grp(Pow(alpha, D(2))), Grp(n), Comma, Sp,
                gamma, Sp, Eq, Sp, Frac,
                Grp(D(1), Plus, c, alpha, Plus, v, beta), Grp(D(3)), Comma),
            Seq(Call("IsIntegral", integer, alpha), Sp, Land, Sp,
                Call("IsIntegral", integer, beta), Sp, Land, Sp,
                Call("IsIntegral", integer, gamma), Comma),
            Seq(basisOne, Sp, Land, Sp, basisTwo, Comma),
            Seq(discrOne, Sp, Eq, Sp, Minus, D(2, 7), Pow(Grp(mn), D(2)), Comma),
            Seq(discrTwo, Sp, Eq, Sp, Minus, D(3), Pow(Grp(mn), D(2)), Dot),
        ]));
    }

    private static Formula Pow(Formula value, Formula exponent) =>
        Seq(value, Caret, Grp(exponent));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
}
