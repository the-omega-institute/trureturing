using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class HeckePoleLatticeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hecke-type factor is meromorphic on the plane with an exact regulator-spaced pole lattice.",
        H("Hecke Pole Lattice"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hecke-factor-has-exact-simple-pole-lattice"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/HeckePoleLattice.hecke_pole_lattice"),
                H("The Hecke factor has exactly the regulator-spaced simple poles"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For eta greater than one, define the k-th Hecke factor as the "
                            + "reciprocal of 1 minus exp((s+2k) log eta). The denominator is "
                            + "entire, so its reciprocal is meromorphic on the whole complex plane.")),
                    Paragraph(Text(
                        "The complex exponential equals one exactly at integer multiples of "
                            + "2 pi i. Since log eta is positive and nonzero, solving the resulting "
                            + "linear equation gives precisely -2k + 2 pi i n / log eta. The "
                            + "integer n includes both signs in the source notation.")),
                    Paragraph(Text(
                        "At every denominator zero its derivative is -log eta, hence nonzero. "
                            + "Mathlib's analytic-order criterion gives denominator order one, and "
                            + "the inverse-order law gives factor order minus one. Away from the "
                            + "lattice the order is zero, proving the displayed biconditional.")),
                    Paragraph(Text(
                        "This formalizes the exact pole mechanism of the source Hecke grid. It "
                            + "does not identify the source's Beatty-Dirichlet series with this "
                            + "factor without an independently supplied analytic factorization."))),
                DescribeRole.Theorem)),
        []));

    private static Formula TheoremFormula()
    {
        Formula eta = F.Id("eta");
        Formula k = F.Id("k");
        Formula n = F.Id("n");
        Formula s = F.Id("s");
        Formula pSubK = F.Seq(F.Id("P"), F.Underscore, F.Grp(k));
        Formula shifted = F.Seq(
            F.Open, s, F.Sp, F.Plus, F.Sp, F.D(2), F.Times, F.Sp, k, F.Close,
            F.Sp, F.Log, F.Sp, eta);
        Formula factorDefinition = F.Seq(
            Call("P", k, s), F.Sp, F.Colon, F.Eq, F.Sp,
            Power(F.Grp(F.D(1), F.Sp, F.Minus, F.Sp, Call("exp", shifted)),
                F.Seq(F.Minus, F.D(1))));
        Formula meromorphic = Call("MeromorphicOn", pSubK, ComplexNumbers());
        Formula pole = F.Seq(
            F.Minus, F.D(2), F.Times, F.Sp, k, F.Sp, F.Plus, F.Sp,
            Fraction(
                F.Seq(F.D(2), F.Pi, F.Sp, F.Id("i"), F.Sp, n),
                F.Seq(F.Log, F.Sp, eta)));
        Formula exactOrder = F.Seq(
            Call("meromorphicOrderAt", pSubK, s), F.Sp, F.Eq, F.Sp,
            F.Minus, F.D(1), F.Sp, F.Iff, F.Sp,
            F.Exists, F.Sp, n, F.Sp, F.InMacro, F.Sp, IntegerNumbers(), F.Comma,
            F.Sp, s, F.Sp, F.Eq, F.Sp, pole);

        return F.Disp(new Formula.Aligned([
            F.Seq(eta, F.Gt, F.D(1), F.Comma, F.Sp, factorDefinition, F.Comma),
            F.Seq(F.Forall, F.Sp, k, F.Sp, F.InMacro, F.Sp, NaturalNumbers(), F.Comma,
                F.Sp, meromorphic, F.Sp, F.Land),
            F.Seq(F.Forall, F.Sp, s, F.Sp, F.InMacro, F.Sp, ComplexNumbers(), F.Comma,
                F.Sp, exactOrder, F.Dot),
        ]));
    }

    private static Formula Power(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        F.Seq(F.Frac, F.Grp(numerator), F.Grp(denominator));

    private static Formula NaturalNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("N")));

    private static Formula IntegerNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("Z")));

    private static Formula ComplexNumbers() =>
        F.Seq(F.Mathbb, F.Grp(F.Id("C")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
