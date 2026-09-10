using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class IterateProductNineModThreeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/IterateProductNineModThree.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a396793");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every coefficient above degree one in OEIS A396793 is divisible by three.",
        H("Hanna's Iterate-Product Congruence Modulo Three"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS A396793 entry states the generating "
                + "equation and conjecture recorded in hanna2026a396793. All series below "
                + "have integer coefficients, and all coefficient indices are natural numbers. "
                + "The normalization is zero constant coefficient and coefficient one at degree one.")),
            Paragraph(Text("PowerSeries(Z) denotes the formal power-series ring with "
                + "indeterminate X. The iterate operation is defined in "
                + "D5/S1/Recurrence/Invariants/CompositionalIterateCongruence: "
                + "iterate(Z,f,0)=X and iterate(Z,f,j+1)=iterate(Z,f,j).subst(f). "
                + "Thus iterate(Z,f,2)=f(f(X)) when the constant coefficient is zero. "
                + "Powers and products are ordinary power-series operations. The operator "
                + "choose selects a witness of the displayed proved existential proposition.")),
            Node("lift_mod_nine", "The lift from modulo three to modulo nine", LiftFormula(),
                "Write f=X+3B using coefficientwise exact integer division. Over ZMod(9), "
                + "the scalar 3 has square zero. The factorization of u^k-v^k shows that "
                + "3(B(X+3B)-B(X))=0, so the second iterate is X+6B. Multiplying "
                + "X+3B by X+6B gives X squared modulo nine. Mapping coefficients "
                + "back to integers gives the displayed divisibility at every degree."),
            Node("generatingSeries", "The normalized generating series", GeneratingFormula(),
                "Existence follows from successive coefficient corrections starting at X. "
                + "At degree n greater than one, the error at degree n+1 is divided by "
                + "three using integer division. The lifting lemma makes this exact and "
                + "makes the correction divisible by three. The stabilized coefficients "
                + "give an integer series satisfying all three existential clauses.",
                DescribeRole.Definition),
            Node("a", "The coefficient sequence", CoefficientFormula(),
                "The integer a(n) is the degree-n coefficient of generatingSeries. "
                + "Its constant coefficient is zero and its degree-one coefficient is one.",
                DescribeRole.Definition),
            Node("generating_equation", "The OEIS equation and normalization", EquationFormula(),
                "The constructed series satisfies the product equation as a formal "
                + "power-series identity, together with both normalization conditions. "
                + "Witness selection preserves these three proved properties."),
            Node("generating_unique", "Uniqueness of the normalized integer solution", UniqueFormula(),
                "If two normalized series agree below degree n greater than one, their "
                + "second iterates differ at degree n by twice their coefficient difference. "
                + "Their products differ at degree n+1 by three times that difference. "
                + "Equal products force equal coefficients over the integers, and strong "
                + "induction proves equality of the series."),
            Node("hanna_conjecture", "The A396793 divisibility conjecture", ConjectureFormula(),
                "Induct on n and truncate the solution below degree n. The earlier "
                + "coefficients make this prefix congruent to X modulo three. The lifting "
                + "lemma makes its product error divisible by nine. Comparing the prefix "
                + "with the solution using the coefficient perturbation gives nine "
                + "dividing 3a(n), hence three dividing a(n), for every n greater than one.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a396793-iterate-product-nine-mod-three"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a396793-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula Generating() => Named("generatingSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Product(Formula f) => Mul(f, Call("iterate", Integers(), f, D(2)));
    private static Formula RightSide() => Add(Power(X(), D(2)), Mul(D(9), Power(X(), D(3))));
    private static Formula NormalizedEquation(Formula f) => Seq(
        Parenthesized(Equal(Product(f), RightSide())), Sp, Land, Sp,
        Parenthesized(Seq(Parenthesized(Equal(Call("constantCoeff", f), D(0))), Sp, Land, Sp,
            Parenthesized(Equal(Call("coeff", D(1), f), D(1))))));

    private static Formula LiftFormula() => Disp(Seq(Bound("f", Series()),
        Implication(Equal(Call("constantCoeff", F.Id("f")), D(0)),
            Implication(Seq(Bound("n", Naturals()),
                    Divides(D(3), Call("coeff", F.Id("n"), Subtract(F.Id("f"), X())))),
                Seq(Bound("n", Naturals()),
                    Divides(D(9), Call("coeff", F.Id("n"),
                        Subtract(Product(F.Id("f")), Power(X(), D(2))))))))));

    private static Formula GeneratingFormula() => Disp(Equal(Generating(),
        Call("choose", Seq(Exists, Sp, F.Id("f"), Colon, Sp, Series(), Comma, Sp,
            Parenthesized(NormalizedEquation(F.Id("f")))))));

    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a", F.Id("n")), Call("coeff", F.Id("n"), Generating()))));

    private static Formula EquationFormula() => Disp(NormalizedEquation(Generating()));

    private static Formula UniqueFormula() => Disp(Seq(Bound("f", Series()),
        Implication(Equal(Product(F.Id("f")), RightSide()),
            Implication(Equal(Call("constantCoeff", F.Id("f")), D(0)),
                Implication(Equal(Call("coeff", D(1), F.Id("f")), D(1)),
                    Equal(F.Id("f"), Generating()))))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Lt, Sp, F.Id("n")),
            Divides(D(3), Call("a", F.Id("n"))))));
}
