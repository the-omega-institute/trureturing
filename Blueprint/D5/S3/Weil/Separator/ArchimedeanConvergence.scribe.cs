using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Separator;

internal sealed class ArchimedeanConvergenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Separator/ArchimedeanConvergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every repository Weil test function is archimedean-convergent, so the "
            + "prime-side Weil criterion needs no separate integrability hypothesis.",
        H("Archimedean Convergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("archimedean-convergent-of-weil-test-function"),
                DeclarationHandle.Create(
                    Prefix + "archimedeanConvergent_of_weilTestFunction"),
                H("Every Weil test function is archimedean-convergent"),
                StatementSource.FromAuthor(ArchimedeanConvergenceStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Here WeilTestFunction is this repository's even, smooth, compactly "
                            + "supported test-function carrier. Closed-strip decay of its "
                            + "Fourier-Laplace transform supplies quadratic decay on the "
                            + "real axis.")),
                    Paragraph(Text(
                        "The digamma vertical-growth bound needed for integrability comes "
                            + "from this repository's Zeta23 layer. The pinned Mathlib has no "
                            + "corresponding bound; the proof binds the frozen Zeta23 "
                            + "gamma-factor integrability theorem and gamma bracket."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rh-iff-prime-side-positivity"),
                DeclarationHandle.Create(Prefix + "rh_iff_primeSidePositivity"),
                H("RH is equivalent to prime-side positivity without hArch"),
                StatementSource.FromAuthor(PrimeSideCriterionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The frozen explicit-formula Weil criterion is instantiated with the "
                            + "preceding convergence theorem for each convolution square. No "
                            + "new explicit-formula or Weil-positivity argument is reproved.")),
                    Paragraph(Text(
                        "The equivalence is relative to a supplied ZeroData only. Existence "
                            + "of ZeroData is not asserted, and M1-b remains open.")),
                    Paragraph(Text(
                        "Its quantifier ranges over this repository's WeilTestFunction. This "
                            + "hArch-free reformulation is not a proof of the Riemann hypothesis."))),
                DescribeRole.Theorem)),
        []));

    private static Formula ArchimedeanConvergenceStatement()
    {
        Formula test = F.Id("g");
        Formula variable = F.Id("t");
        Formula integrand = Call("archimedeanIntegrand", test, variable);
        Formula integral = Call("Integrable", Lambda(variable, integrand));

        return Disp(ForAll(
            [Bound("g", F.Id("WeilTestFunction"))],
            integral));
    }

    private static Formula PrimeSideCriterionStatement()
    {
        Formula zeroData = F.Id("Z");
        Formula test = F.Id("g");
        Formula square = Call("convolutionSquare", test);
        Formula convergence = Call(
            "archimedeanConvergentOfWeilTestFunction", square);
        Formula primeSide = Add(
            Subtract(Call("poleTerm", square), Call("primeTerm", square)),
            Call("archimedeanTerm", square, convergence));
        Formula positivity = ForAll(
            [Bound("g", F.Id("WeilTestFunction"))],
            LessOrEqual(D(0), RealPart(primeSide)));

        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroData"))],
            Iff(RiemannHypothesis(), positivity)));
    }

    private static Formula RiemannHypothesis() =>
        Seq(Operatorname, Grp(F.Id("RiemannHypothesis")));

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula Lambda(Formula variable, Formula body) =>
        Seq(Open, variable, Sp, Mapsto, Sp, body, Close);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(
            left, FormulaRelationOperator.LessThanOrEqual, right);
}
