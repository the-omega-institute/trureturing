using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ControlledLearning;

internal sealed class RepeatedSpectrumPassiveFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated positive spectra have an exact commutant fiber for two passive learning steps.",
        H("Repeated-spectrum passive observation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-step-outputs-iff-commuting-difference"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ControlledLearning/RepeatedSpectrumPassiveFiber."
                    + "two_step_outputs_iff_commuting_difference"),
                H("Complete two-step output fiber, including resonance"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be a finite real diagonal matrix with positive diagonal entries. "
                        + "Consider two pairs of symmetric external Gram blocks, the same S as "
                        + "initial output, and nonzero step sizes eta and tau. Each step is the "
                        + "exact simultaneous gradient-descent recurrence for the fixed loss "
                        + "one half of the squared Frobenius norm of the two-layer output. "
                        + "The first and second outputs agree exactly when there is a symmetric "
                        + "X with A2=A1+X, B2=B1-X, X S=S X, and D X commuting with the first "
                        + "output, where D=I-eta-squared S-squared.")),
                    Paragraph(Text(
                        "The first-step equality determines the full difference of symmetric "
                        + "matrix entries. Positivity of the sum of two diagonal entries forces "
                        + "the two block differences to be opposite; the same equations then "
                        + "force commutation with S. Transport through the actual first step "
                        + "gives D X and minus D X, so the second output detects precisely their "
                        + "commutator with the observed first output. No distinct-eigenvalue "
                        + "assumption or inverse of D is used. Repeated eigenvalues and erased "
                        + "resonant directions are included.")),
                    Paragraph(Text(
                        "The classification concerns symmetric-block recurrences. "
                        + "Physical Gram states additionally require positivity and a width "
                        + "rank bound. Generic four-step identification, resonance collapse "
                        + "and quantitative prediction require additional hypotheses and are "
                        + "not conclusions of this theorem."))),
                DescribeRole.Theorem)),
        []));

    private static Formula TheoremFormula()
    {
        var sigma = SigmaLower;
        var eta = F.Id("eta");
        var tau = F.Id("tau");
        var s = F.Id("S");
        var d = F.Id("D");
        var x = F.Id("X");
        var aOne = Indexed("A", 1);
        var bOne = Indexed("B", 1);
        var aTwo = Indexed("A", 2);
        var bTwo = Indexed("B", 2);
        var matrix = Call("Matrix", F.Id("I"), F.Id("I"), RealNumbers());
        var firstOne = Call("outputStep", aOne, bOne, s, eta);
        var firstTwo = Call("outputStep", aTwo, bTwo, s, eta);
        var secondOne = Call("twoStepOutput", aOne, bOne, s, eta, tau);
        var secondTwo = Call("twoStepOutput", aTwo, bTwo, s, eta, tau);
        var transportedDifference = Parenthesized(Product(d, x));

        var hypotheses = Conjoin(
            Seq(Forall, Sp, F.Id("i"), Sp, InMacro, Sp, F.Id("I"), Comma, Sp,
                D(0), Sp, Lt, Sp, Indexed(sigma, F.Id("i"))),
            Equal(Transpose(aOne), aOne),
            Equal(Transpose(bOne), bOne),
            Equal(Transpose(aTwo), aTwo),
            Equal(Transpose(bTwo), bTwo),
            Seq(eta, Sp, Neq, Sp, D(0)),
            Seq(tau, Sp, Neq, Sp, D(0)));

        var observedEqualities = Parenthesized(Conjoin(
            Equal(firstOne, firstTwo),
            Equal(secondOne, secondTwo)));

        var witness = Seq(
            Exists, Sp, x, Sp, InMacro, Sp, matrix, Comma, Sp,
            Parenthesized(Conjoin(
                Equal(Transpose(x), x),
                Equal(Product(x, s), Product(s, x)),
                Equal(aTwo, Seq(aOne, Sp, Plus, Sp, x)),
                Equal(bTwo, Seq(bOne, Sp, Minus, Sp, x)),
                Equal(Product(transportedDifference, firstOne),
                    Product(firstOne, transportedDifference)))));

        return Disp(Seq(
            Forall, Sp, sigma, Colon, Sp, F.Id("I"), To, RealNumbers(), Comma, Esc,
            Forall, Sp, aOne, Comma, Sp, bOne, Comma, Sp, aTwo, Comma, Sp, bTwo,
                Sp, InMacro, Sp, matrix, Comma, Esc,
            Forall, Sp, eta, Comma, Sp, tau, Sp, InMacro, Sp, RealNumbers(), Comma, RowBreak,
            s, Sp, Eq, Sp, Call("diagonal", sigma), Comma, Sp,
            d, Sp, Eq, Sp, Seq(D(1), Sp, Minus, Sp, Squared(eta), Sp, Cdot, Sp, Squared(s)),
                Comma, RowBreak,
            hypotheses, Sp, Rightarrow, Sp,
            Parenthesized(Seq(observedEqualities, Sp, Iff, Sp, witness)), Dot));
    }

    private static Formula RealNumbers() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Indexed(string name, byte index) => Indexed(F.Id(name), D(index));

    private static Formula Indexed(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Transpose(Formula value) => Seq(value, Caret, Grp(F.Id("T")));

    private static Formula Squared(Formula value) => Seq(value, Caret, Grp(D(2)));

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Conjoin(params Formula[] values)
    {
        var result = values[0];
        for (var index = 1; index < values.Length; index++)
        {
            result = Seq(result, Sp, Land, RowBreak, values[index]);
        }

        return result;
    }
}
