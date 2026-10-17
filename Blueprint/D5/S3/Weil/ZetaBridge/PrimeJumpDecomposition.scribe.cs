using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class PrimeJumpDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The finite prime-power term is coherent mass minus a nonnegative translation energy, "
            + "and that energy is the quadratic form of the arithmetic jump Laplacian.",
        H("Prime Jump Decomposition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-jump-decomposition"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaBridge/PrimeJumpDecomposition.prime_jump_decomposition"),
                H("Prime jump decomposition"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The test function lies in the canonical carrier of even smooth compactly "
                            + "supported complex-valued functions. The displayed support witness "
                            + "places its support inside the interval from minus L to L.")),
                    Paragraph(Text(
                        "The active channels are the prime powers at or below exp(2L), filtered by "
                            + "nonzero von Mangoldt weight. Their critical-line weights are summed "
                            + "to form the coherent mass and weight the squared translation "
                            + "displacements in the arithmetic energy.")),
                    Paragraph(Text(
                        "For the concrete same-window L2 application documented with "
                            + "WeilMellinPrimeIntertwining.primeSymmetric, use this source's "
                            + "activePrimePowers, primeWeight and totalPrimeWeight unchanged. "
                            + "With P_L the actual interval-indicator projection and "
                            + "T_s=P_L U_s P_L, the corresponding bounded unsigned block is "
                            + "sum_n primeWeight(n)*(T_log(n)+T_{-log(n)}). Its norm is at most "
                            + "2*totalPrimeWeight(L), because both compressed translations "
                            + "are contractions and every weight is nonnegative. Its exact "
                            + "finite representative retains every prime power and agrees "
                            + "almost everywhere with the existing primeSymmetric at cutoff "
                            + "floor(exp(2L)). The equality channel log(n)=2L is the zero "
                            + "compressed operator, while the definition of totalPrimeWeight "
                            + "still includes that channel's weight. The displayed "
                            + "arithmeticJumpLaplacian keeps its original full-space pointwise "
                            + "definition and smooth even test-function hypotheses.")),
                    Paragraph(Text(
                        "All three source clauses are public: the exact complex prime-term "
                            + "decomposition, nonnegativity of the independently constructed "
                            + "energy, and its equality with the real part of the explicit "
                            + "Laplacian quadratic form."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula test = F.Id("f");
        Formula scale = F.Id("L");
        Formula variable = F.Id("y");
        Formula supportWitness = F.Id("hSupport");
        Formula convolutionSquare = Call("convolutionSquare", test);
        Formula primeTerm = Call("primeTerm", convolutionSquare);
        Formula totalWeight = Call("totalPrimeWeight", scale);
        Formula mass = Call("l2Mass", test);
        Formula energy = Call("arithmeticJumpEnergy", scale, test);
        Formula laplacian = Call("arithmeticJumpLaplacian", scale, test, variable);
        Formula supportInterval = Seq(
            OpenBracket, Minus, scale, Comma, Sp, scale, CloseBracket);
        Formula coherentMass = new Formula.Binary(
            new Formula.Binary(D(2), FormulaBinaryOperator.Multiply, totalWeight),
            FormulaBinaryOperator.Multiply,
            mass);
        Formula decomposition = new Formula.Relation(
            primeTerm,
            FormulaRelationOperator.Equal,
            new Formula.Binary(coherentMass, FormulaBinaryOperator.Subtract, energy));
        Formula nonnegative = new Formula.Relation(
            D(0), FormulaRelationOperator.LessThanOrEqual, energy);
        Formula integrand = new Formula.Binary(
            Call("conj", Call("f", variable)),
            FormulaBinaryOperator.Multiply,
            laplacian);
        Formula quadraticForm = Seq(
            Re, Open, Int, Underscore, Grp(Mathbb, Grp(F.Id("R"))), Sp,
            integrand, Sp, F.Id("d"), variable, Close);
        Formula laplacianIdentity = new Formula.Relation(
            energy, FormulaRelationOperator.Equal, quadraticForm);
        Formula conclusion = new Formula.Logic(
            decomposition,
            FormulaLogicOperator.And,
            new Formula.Logic(
                nonnegative,
                FormulaLogicOperator.And,
                laplacianIdentity));

        return Disp(Seq(
            Forall, Sp, test, InMacro, Sp, Mathcal, Grp(F.Id("W")), Comma, Sp,
            scale, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            supportWitness, Colon, Sp,
            Call("tsupport", test), Sp, Subseteq, Sp, supportInterval,
            Sp, Rightarrow, Sp, conclusion));
    }
}
