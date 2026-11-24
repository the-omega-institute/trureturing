using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class CyclicCollisionCertificateDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/CyclicCollisionCertificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Certified lattice coordinates give upper and lower collision bounds through a finite character sum.",
        H("Lattice Enclosures and Cyclic Collision Mass"),
        Blocks(
            Paragraph(Text(
                "Use a finite coordinate set, real frequencies g(j), integer approximations a(j), "
                + "and weights w(j). Let E(t) be the sum of products of weighted multinomial "
                + "coefficients of ordered degree-p pairs with real frequency gap at most t. "
                + "Their lattice coordinates are the integer sums of a(j) with the same counts. "
                + "Let C(R) count the same weighted ordered pairs whose lattice difference modulo q "
                + "belongs to a finite residue set R. Write R(H) for the image of the integer interval "
                + "from −H to H in ZMod q. Each residue occurs only once.")),
            Paragraph(Text(
                "For both transfers below the weights are nonnegative, the lattice step s and "
                + "the coordinate error e satisfy s≥0 and e≥0, and |g(j)−s a(j)|≤e for every j. "
                + "For the first transfer take s>0 and let H be the floor of (t+2pe)/s.")),
            Describe.Lean(
                DescribeId.Create("tail-to-cyclic"),
                DeclarationHandle.Create(Owner + ".tailCollisionMass_le_cyclic"),
                H("The modular band contains the real near-collisions"),
                StatementSource.FromAuthor(Disp(AtMost(Call("E", F.Id("t")),
                    Call("C", Call("R", F.Id("H")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signed difference "
                    + "of the errors is bounded by e times the sum of the absolute count "
                    + "differences. For two degree-p vectors that sum is at most 2p."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the reverse transfer assume each a(j) lies in an integer interval [l,u] "
                + "and p(u−l)+H<q.")),
            Describe.Lean(
                DescribeId.Create("cyclic-to-tail"),
                DeclarationHandle.Create(Owner + ".cyclicCollisionMass_le_tail_of_no_wrap"),
                H("A bounded lattice spread excludes wraparound"),
                StatementSource.FromAuthor(Disp(AtMost(Call("C", Call("R", F.Id("H"))),
                    Call("E", Add(Multiply(F.Id("s"), F.Id("H")),
                        Multiply(Multiply(D(2), F.Id("p")), F.Id("e"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Congruent integers differ by a multiple of q. The spread of the "
                    + "degree-p lattice sums makes this multiple zero for a residue in R(H). "
                    + "The strict inequality excludes aliasing at an endpoint."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "For the Fourier identity assume q>0. Write S(k)=Σ w(j)χ(k,a(j)), "
                + "where χ(k,x) is the positive standard character at x in ZMod q.")),
            Describe.Lean(
                DescribeId.Create("cyclic-collision-fourier"),
                DeclarationHandle.Create(Owner + ".cyclicCollisionMass_fourier"),
                H("Character orthogonality evaluates the cyclic mass"),
                StatementSource.FromAuthor(Fourier()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The multinomial expansion "
                        + "of the power gives the weighted character sum over the degree vectors. "
                        + "Conjugation introduces the second vector with opposite sign, and the "
                        + "sum over characters retains exactly the differences in R.")),
                    Paragraph(Text(
                        "With certified enclosures for fixed ζ ordinates, the first transfer and "
                        + "the exact Fourier identity give a finite upper certificate. A bound "
                        + "with the required degree, resolution and computational cost is still open."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Fourier()
    {
        var q = F.Id("q");
        var p = F.Id("p");
        var r = F.Id("R");
        var k = F.Id("k");
        var y = F.Id("y");
        var amplitude = new Formula.Power(new Formula.Absolute(Call("S", k)), Multiply(D(2), p));
        var kernel = Seq(new Formula.Subscript(Sum, Seq(y, Sp, InMacro, Sp, r)), Sp,
            Call("chi", k, Seq(Minus, y)));
        var average = Seq(new Formula.Subscript(Sum, Seq(k, Sp, InMacro, Sp, Call("ZMod", q))), Sp,
            Multiply(amplitude, Seq(Open, kernel, Close)));
        return Disp(new Formula.Relation(Multiply(q, Call("C", r)), FormulaRelationOperator.Equal, average));
    }
}
