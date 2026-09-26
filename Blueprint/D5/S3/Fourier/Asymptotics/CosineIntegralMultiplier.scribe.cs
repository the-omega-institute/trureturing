using System.Collections.Immutable;
using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class CosineIntegralMultiplierDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CosineIntegralMultiplier.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual cosine-integral tail has an exact Fourier transform in complex Lebesgue L2 at every positive scale.",
        H("The Cosine-Integral Fourier Multiplier"),
        Blocks(
            Describe.Lean(DescribeId.Create("cosine-integral-kernel"),
                DeclarationHandle.Create(Module + "q"), H("The spatial kernel"),
                StatementSource.FromAuthor(KernelFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The function q(c,x) is the complex embedding of 2 Ci(c|x|). "
                    + "Ci is the existing real function sin(x)/x minus the integral of "
                    + "sin(t)/t^2 over t>x. For x>0 this tail integral converges absolutely. "
                    + "The definition gives a value at zero, whose choice does not affect its L2 class."),
                    Ref("D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral"),
                    Ref("D5/L/Fourier/nist2026cosineintegral"))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("frequency-multiplier"),
                DeclarationHandle.Create(Module + "m"), H("The frequency function"),
                StatementSource.FromAuthor(MultiplierFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real value -1/|xi| is embedded into the complex numbers when "
                    + "|xi| is at least c/(2 pi); the value is zero below this threshold. "
                    + "Here ite selects its second argument when its first argument holds, "
                    + "and its third argument otherwise. For c>0 the support is unbounded "
                    + "and avoids a neighborhood of zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exact-l2-fourier-transform"),
                DeclarationHandle.Create(Module + "result"), H("Every positive real scale"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real c>0, both q(c) and m(c) belong to complex L2 of "
                        + "Lebesgue measure on the real line. FourierL2 denotes the actual "
                        + "Fourier linear isometry equivalence with phase exp(-2 pi i x xi); "
                        + "class denotes the almost-everywhere quotient class constructed "
                        + "using the established membership. The theorem proves equality "
                        + "of these Lp elements. No integrability or transform identity is assumed.")),
                    Paragraph(Text(
                        "On a finite positive frequency interval [a,b], reflect the "
                        + "integrable function -1/xi to the negative interval. Its inverse "
                        + "Fourier integral is 2(Ci(2 pi a|x|)-Ci(2 pi b|x|)) for x nonzero. "
                        + "Integration by parts in the convergent sine tail establishes "
                        + "the finite-interval cosine identity. The two complex exponential "
                        + "terms combine to twice the real cosine.")),
                    Paragraph(Text(
                        "Fourier duality against Schwartz functions and the injective "
                        + "embedding of L2 into tempered distributions identify the finite-band "
                        + "integral with the actual inverse L2 transform. The spatial and "
                        + "frequency tails both have squared L2 norm 4 pi/c. The spatial "
                        + "identity follows from the cosine-integral Gram formula. Sending "
                        + "the upper frequency cutoff to infinity therefore gives actual "
                        + "L2 convergence on both sides, and continuity of the Fourier "
                        + "isometry gives the asserted equality."),
                        Ref("D5/S3/Fourier/Asymptotics/CosineIntegralGram.result")),
                    Paragraph(Text(
                        "Changing values at zero or at either threshold does not change "
                        + "the quotient classes. In angular frequency zeta=2 pi xi the "
                        + "same multiplier is -2 pi/|zeta| for |zeta|>=c, and zero otherwise. "
                        + "The weighted integral-operator norm bound requires its own "
                        + "operator representation and estimate; it is not asserted here. "
                        + "No mixed process limit is asserted."))), DescribeRole.Theorem))));

    private static Formula Reals => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula ForAll(Formula body, params string[] names) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            names.Select(name => new Formula.BoundVariable(FormulaIdentifier.Create(name), Reals)).ToImmutableArray(), body);

    private static Formula KernelFormula()
    {
        Formula c = F.Id("c"), x = F.Id("x");
        return F.Disp(ForAll(Equal(Call("q", c, x), Call("ofReal",
            Multiply(F.D(2), Call("Ci", Multiply(c, new Formula.Absolute(x)))))), "c", "x"));
    }

    private static Formula MultiplierFormula()
    {
        Formula c = F.Id("c"), xi = F.Id("xi"), abs = new Formula.Absolute(xi);
        Formula cutoff = new Formula.Relation(new Formula.Fraction(c, Multiply(F.D(2), F.Pi)),
            FormulaRelationOperator.LessThanOrEqual, abs);
        return F.Disp(ForAll(Equal(Call("m", c, xi), Call("ofReal", Call("ite", cutoff,
            new Formula.Fraction(new Formula.Negate(F.D(1)), abs), F.D(0)))), "c", "xi"));
    }

    private static Formula ResultFormula()
    {
        Formula c = F.Id("c"), q = Call("q", c), m = Call("m", c);
        Formula body = And(Call("MemLp", q, F.D(2), Call("Lebesgue")),
            And(Call("MemLp", m, F.D(2), Call("Lebesgue")),
                Equal(Call("FourierL2", Call("class", q)), Call("class", m))));
        return F.Disp(ForAll(new Formula.Logic(
            new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, c),
            FormulaLogicOperator.Implies, body), "c"));
    }
}
