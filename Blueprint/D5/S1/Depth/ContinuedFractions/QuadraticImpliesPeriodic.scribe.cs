using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Depth.ContinuedFractions;

internal sealed class QuadraticImpliesPeriodicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniformly bounded integral quadratic certificates reduce complete quotients to a "
            + "finite state space and force eventual periodicity.",
        H("Bounded Complete Quotients Force Periodicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nonzero-coefficients-give-a-nonzero-polynomial"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic."
                        + "quadraticPolynomial_ne_zero"),
                H("A nonzero coefficient triple gives a nonzero polynomial"),
                StatementSource.FromAuthor(NonzeroPolynomialFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An integral triple (a,b,c) encodes the real polynomial "
                            + "a t^2+b t+c. If the encoded polynomial vanished identically, "
                            + "its coefficients in degrees two, one, and zero would all vanish, "
                            + "contradicting the assumption that the triple is nonzero.")),
                    Paragraph(Text(
                        "This is a statement about the polynomial itself. It does not assert "
                            + "irreducibility, degree exactly two, or the existence of a root."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("bounded-complete-quotients-force-eventual-periodicity"),
                DeclarationHandle.Create(
                    "D5/S1/Depth/ContinuedFractions/QuadraticImpliesPeriodic."
                        + "quadratic_irrational_eventually_periodic_of_bounded_complete_quotients"),
                H("Bounded complete quotients force eventual periodicity"),
                StatementSource.FromAuthor(EventualPeriodicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume x is a quadratic irrational and every complete quotient of x "
                            + "satisfies a nonzero integral quadratic whose three coefficients "
                            + "share one uniform bound. Only finitely many coefficient triples "
                            + "can then occur, and each corresponding nonzero polynomial has "
                            + "only finitely many real roots. The complete quotients therefore "
                            + "range over a finite set.")),
                    Paragraph(Text(
                        "Two complete quotients must consequently coincide. The shift lemma "
                            + "turns that repeated state into a positive period for every later "
                            + "continued-fraction coefficient. The bounded certificate is an "
                            + "explicit hypothesis here: this module does not prove that every "
                            + "quadratic irrational supplies such a uniform bound."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() =>
        Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Integers() =>
        Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula Triple(Formula first, Formula second, Formula third) =>
        Seq(Open, first, Comma, Sp, second, Comma, Sp, third, Close);

    private static Formula Coefficient(Formula value, Formula index) =>
        Call("coefficient", value, index);

    private static Formula NonzeroPolynomialFormula()
    {
        Formula coefficients = F.Id("u");
        Formula integerTriples = Seq(Integers(), Caret, Grp(D(3)));

        return Disp(Seq(
            Forall, Sp, coefficients, Sp, InMacro, Sp, integerTriples, Comma, Sp,
            coefficients, Sp, Neq, Sp, Triple(D(0), D(0), D(0)), Sp,
            Rightarrow, Sp,
            Call("quadraticPolynomial", coefficients), Sp, Neq, Sp, D(0), Dot));
    }

    private static Formula EventualPeriodicityFormula()
    {
        Formula value = F.Id("x");
        Formula start = F.Id("s");
        Formula period = F.Id("p");
        Formula offset = F.Id("k");
        Formula startAndOffset = Seq(start, Sp, Plus, Sp, offset);

        return Disp(Seq(
            Forall, Sp, value, Sp, InMacro, Sp, Reals(), Comma, Sp,
            Open,
            Call("IsQuadraticIrrational", value), Sp, Land, Sp,
            Call("BoundedCompleteQuotientCertificate", value),
            Close, Sp, Rightarrow, Sp,
            Exists, Sp, start, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Exists, Sp, period, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            D(0), Sp, Lt, Sp, period, Sp, Land, Sp,
            Forall, Sp, offset, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Coefficient(
                value,
                Seq(startAndOffset, Sp, Plus, Sp, period)),
            Sp, Eq, Sp,
            Coefficient(value, startAndOffset), Dot));
    }
}
