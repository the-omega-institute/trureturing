using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class OffLineZeroNegativeLiteralRationalEnergyDocument
    : IScribeDocumentDefinition
{
    private const string Result =
        "D5/S3/Weil/Separator/OffLineZeroNegativeLiteralRationalEnergy."
        + "offLineZero_yields_negative_literal_rational_energy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A stored off-line zero produces an exact literal rational smooth-transition "
            + "test with a negative complete paired zero sum and the same negative full energy.",
        H("Negative Full Energy in the Literal Rational Family"),
        Blocks(
            Describe.Lean(DescribeId.Create("offline-zero-literal-rational-energy"),
                DeclarationHandle.Create(Result),
                H("An off-line zero yields a literal negative-energy test"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("ZeroData stores distinct nontrivial zeros with their "
                        + "analytic multiplicities. The hypothesis refers to one actual "
                        + "stored index, whose real part differs from criticalAbscissa. "
                        + "Neither an off-line zero nor ZeroData is asserted to exist.")),
                    Paragraph(Text("The natural radius R is strictly positive. The rational "
                        + "polynomials p and q are evaluated by rationalEvenPolynomial, the "
                        + "even complex polynomial pair. The displayed pointwise equality "
                        + "is the function equality in the Lean statement. The support "
                        + "enclosure is [-2R,2R], not an assertion of support equality.")),
                    Paragraph(Text("The literal cutoff is smoothTransition(2-|x|/R). Its "
                        + "smoothness uses the explicit inner-product bump base at parameter "
                        + "2 and argument x/R. Rational approximation of three physical jets "
                        + "on the entire support interval controls the cutoff product error. "
                        + "A full summable fourth moment then bounds the paired transform "
                        + "difference at gamma and conjugate gamma, retaining multiplicities "
                        + "and the strict margin of the original negative test.")),
                    Paragraph(Text("The zero-side convergence proof is "
                        + "symmetricConvergent_of_zeroData for convolutionSquare(h). The "
                        + "energy identity also uses archimedeanConvergent_of_weilTestFunction "
                        + "for the same square. The support scale passed to the identity is "
                        + "L=2R, so its arithmetic cutoff is exp(4R). All integrals use "
                        + "Lebesgue measure on the real line.")),
                    Paragraph(Text("This is erased analytic existence. It supplies no "
                        + "degree or denominator bound, numerical certificate, executable "
                        + "search, or proof of the Riemann hypothesis."))),
                DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula z = F.Id("Z"), n = F.Id("n"), r = F.Id("R");
        Formula p = F.Id("p"), q = F.Id("q"), h = F.Id("h"), x = F.Id("x");
        Formula square = Call("convolutionSquare", h);
        Formula zeroSide = Call("zeroSum", z, square,
            Call("symmetricConvergentOfZeroData", z, square));
        Formula cutoff = Call("ofReal", Call("smoothTransition",
            Subtract(D(2), new Formula.Fraction(new Formula.Absolute(x), r))));
        Formula literal = Multiply(cutoff, Call("rationalEvenPolynomial", p, q, x));
        Formula pointwise = All([Bound("x", Real)], Equal(Call("h", x), literal));
        Formula scale = Multiply(D(2), r);
        Formula support = Rel(Call("tsupport", h), FormulaRelationOperator.SubsetOf,
            Call("Icc", new Formula.Negate(scale), scale));
        Formula energy = FullEnergy(h, scale);
        Formula negative = And(Lt(Call("re", zeroSide), D(0)),
            And(Equal(zeroSide, Call("ofReal", energy)), Lt(energy, D(0))));
        Formula witnesses = Some(
            [Bound("R", Natural), Bound("p", RatPoly), Bound("q", RatPoly),
                Bound("h", F.Id("WeilTestFunction"))],
            And(Lt(D(0), r), And(pointwise, And(support, negative))));
        Formula offLine = NotEqual(Call("re", Call("zero", z, n)),
            F.Id("criticalAbscissa"));
        return Disp(All([Bound("Z", F.Id("ZeroData")), Bound("n", Natural)],
            new Formula.Logic(offLine, FormulaLogicOperator.Implies, witnesses)));
    }

    private static Formula FullEnergy(Formula h, Formula scale)
    {
        Formula x = F.Id("x");
        Formula integrand = Multiply(Call("exp",
            new Formula.Fraction(Call("ofReal", x), D(2))), new Formula.Apply(h, [x]));
        Formula integral = Seq(Int, Underscore, Grp(Real), Sp,
            integrand, Sp, F.Id("d"), x);
        return Subtract(Add(Add(Multiply(D(2), Call("normSq", integral)),
            Call("archimedeanJumpEnergy", h)), Call("arithmeticJumpEnergy", scale, h)),
            Multiply(Subtract(Multiply(D(2), Call("totalPrimeWeight", scale)),
                F.Id("archimedeanConstant")), Call("l2Mass", h)));
    }

    private static Formula Real => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Natural => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RatPoly => Call("Polynomial", Seq(Mathbb, Grp(F.Id("Q"))));
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Some(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
