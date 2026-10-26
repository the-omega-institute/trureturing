using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class ImpreciseCHSHSeparableOptimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/ImpreciseCHSHSeparableOptimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/morelliyamasakihubertavakoli2022imprecise");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The sharp separable CHSH value for two qubits with imprecisely calibrated binary observables is attained and optimal.",
        H("The imprecise separable CHSH optimum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("imprecise-chsh-witness"),
                DeclarationHandle.Create(Prefix + "witness"),
                H("The two-qubit CHSH witness"),
                StatementSource.FromAuthor(Disp(WitnessFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The witness is the real part of the trace of a two-qubit state times the CHSH matrix. "
                    + "The four tensor products use the two local observables on each side, with the fourth term carrying a minus sign."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("imprecise-chsh-admissible"),
                DeclarationHandle.Create(Prefix + "Admissible"),
                H("Calibrated binary observables"),
                StatementSource.FromAuthor(Disp(AdmissibleFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Four qubit observables are admissible when each is binary and their real trace pairings "
                    + "with the target Pauli X or Z matrix are at least 2 minus 4 epsilon, in the order X, Z, X, Z."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("imprecise-chsh-separable-value"),
                DeclarationHandle.Create(Prefix + "separableValue"),
                H("The calibrated separable value"),
                StatementSource.FromAuthor(Disp(SeparableValueFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The value follows the source's two branches. Below the threshold one half minus "
                    + "one over twice the square root of two, it is the explicit expression with a linear "
                    + "calibration term and a square-root term; above the threshold it is the constant two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("imprecise-chsh-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The greatest admissible separable witness value"),
                StatementSource.FromAuthor(Disp(Equivalent(Local("claim"), ClaimBody()))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every epsilon in the unit interval, the displayed separable value is the greatest "
                    + "real number attained by a separable two-qubit state and four admissible binary observables."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("imprecise-chsh-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The separable CHSH optimum is attained and optimal"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For the upper bound, first compute the witness on a tensor product of two Hermitian "
                        + "trace-one positive semidefinite matrices as the CHSH combination of the four local "
                        + "real expectations. A binary observable on a trace-one positive matrix has expectation "
                        + "in the interval from minus one to one, and the scalar CHSH inequality therefore gives "
                        + "the constant bound two.")),
                    Paragraph(Text(
                        "In the small-epsilon branch set c equal to 1 minus 2 epsilon and s equal to twice the "
                        + "square root of epsilon times 1 minus epsilon. Their squares sum to one, and the calibration "
                        + "constraints, together with the Bloch decomposition of each observable, give two unit-circle "
                        + "coordinates whose four expectation magnitudes are bounded by the corresponding ellipse. "
                        + "The rectangle reduction and the ellipse CHSH inequality bound the product witness by "
                        + "2 c s plus the square root of 1 plus (c squared minus s squared) squared. Algebra identifies "
                        + "this with the first branch of separableValue.")),
                    Paragraph(Text(
                        "Every separable state lies in the convex hull of tensor products. The witness is affine in "
                        + "the state, so the tensor-product bound extends to all separable states.")),
                    Paragraph(Text(
                        "For attainment in the small branch, take observables in the XZ plane with vectors (c,0,s) "
                        + "and (s,0,c), and use the explicitly constructed positive trace-one qubit state on both factors. "
                        + "Its top singular direction gives the value 2 c s plus the same square root, while the calibration "
                        + "equalities hold. In the large-epsilon branch the scalar CHSH bound is two; four observables with "
                        + "vector (1 over square root of two, 0, 1 over square root of two) and their corresponding product "
                        + "state attain two. The two cases establish both greatestness and attainment for every epsilon."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("morelli-yamasaki-huber-tavakoli-2022-imprecise-chsh-optimum"),
                    ResolutionKind.Proved))),
        []));

    private static Formula WitnessFormula()
    {
        Formula rho = Rho, a1 = A(1), a2 = A(2), b1 = B(1), b2 = B(2);
        Formula chsh = Sub(Add(Add(Kron(a1, b1), Kron(a1, b2)), Kron(a2, b1)), Kron(a2, b2));
        Formula body = Eq(LocalCall("witness", rho, a1, a2, b1, b2),
            RealPart(Trace(Mul(rho, chsh))));
        return All(rho, StateType(), All(a1, QubitMatrixType(), All(a2, QubitMatrixType(),
            All(b1, QubitMatrixType(), All(b2, QubitMatrixType(), body)))));
    }

    private static Formula AdmissibleFormula()
    {
        Formula epsilon = Epsilon(), a1 = A(1), a2 = A(2), b1 = B(1), b2 = B(2);
        Formula threshold = Sub(R(2), Mul(R(4), epsilon));
        Formula body = And(BinaryObservable(a1),
            And(BinaryObservable(a2),
                And(BinaryObservable(b1),
                    And(BinaryObservable(b2),
                        And(Le(threshold, RealPart(Trace(Mul(a1, QubitX())))),
                            And(Le(threshold, RealPart(Trace(Mul(a2, QubitZ())))),
                                And(Le(threshold, RealPart(Trace(Mul(b1, QubitX())))),
                                    Le(threshold, RealPart(Trace(Mul(b2, QubitZ())))))))))));
        return All(epsilon, Reals(), All(a1, QubitMatrixType(), All(a2, QubitMatrixType(),
            All(b1, QubitMatrixType(), All(b2, QubitMatrixType(),
                Eq(LocalCall("Admissible", epsilon, a1, a2, b1, b2), body))))));
    }

    private static Formula SeparableValueFormula()
    {
        Formula epsilon = Epsilon();
        Formula threshold = Sub(Div(R(1), R(2)),
            Div(R(1), Mul(R(2), Sqrt(R(2)))));
        Formula c = Sub(R(1), Mul(R(2), epsilon));
        Formula rootArgument = Mul(epsilon, Sub(R(1), epsilon));
        Formula first = Mul(Mul(R(4), c), Sqrt(rootArgument));
        Formula second = Sqrt(Sub(R(2), Mul(Mul(Mul(R(16), epsilon),
            Sub(R(1), epsilon)), Pow(c, D(2)))));
        return All(epsilon, Reals(), Eq(LocalCall("separableValue", epsilon),
            If(Le(epsilon, threshold), Add(first, second), R(2))));
    }

    private static Formula ClaimBody()
    {
        Formula epsilon = Epsilon(), w = F.Id("w");
        Formula rho = Rho, a1 = A(1), a2 = A(2), b1 = B(1), b2 = B(2);
        Formula witnesses = SetBuilder(w, Reals(),
            Some(rho, StateType(), Some(a1, QubitMatrixType(), Some(a2, QubitMatrixType(),
                Some(b1, QubitMatrixType(), Some(b2, QubitMatrixType(),
                    And(Separable(rho),
                        And(LocalCall("Admissible", epsilon, a1, a2, b1, b2),
                            Eq(w, LocalCall("witness", rho, a1, a2, b1, b2))))))))));
        Formula interval = Call("Set.Icc", R(0), R(1));
        return All(epsilon, Reals(), Imp(Member(epsilon, interval),
            Call("IsGreatest", witnesses, LocalCall("separableValue", epsilon))));
    }

    private static Formula A(byte index) => Seq(F.Id("a"), Underscore, Grp(D(index)));
    private static Formula B(byte index) => Seq(F.Id("b"), Underscore, Grp(D(index)));
    private static Formula Epsilon() => Varepsilon;
    private static Formula R(byte value) => Typed(value switch
    {
        16 => D(1, 6),
        _ => D(value),
    }, Reals());
    private static Formula FinTwo() => Call("Fin", D(2));
    private static Formula PairIndex() => Parenthesized(Seq(FinTwo(), Sp, Times, Sp, FinTwo()));
    private static Formula QubitMatrixType() => Call("Matrix", FinTwo(), FinTwo(), Complexes());
    private static Formula StateType() => Call("Matrix", PairIndex(), PairIndex(), Complexes());
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Local(string name) => Qualified(
        "D5", "S3", "QuantumBounds", "ImpreciseCHSHSeparableOptimum", name);
    private static Formula Call(string name, params Formula[] arguments) =>
        At(Qualified(name.Split('.')), arguments);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula QubitX() => Qualified("D5", "S3", "Quantum", "FiniteDimensional", "qubitX");
    private static Formula QubitZ() => Qualified("D5", "S3", "Quantum", "FiniteDimensional", "qubitZ");
    private static Formula BinaryObservable(Formula value) => At(Qualified(
        "D5", "S3", "QuantumBounds", "NonlocalityDepthQuantumBound", "IsBinaryObservable"), value);
    private static Formula Separable(Formula value) => At(Qualified(
        "D5", "S3", "Quantum", "Entanglement", "Witness", "WernerTesterIncompleteness", "Separable"), value);
    private static Formula Kron(Formula left, Formula right) =>
        Call("Matrix.kronecker", left, right);
    private static Formula Trace(Formula value) => At(Qualified("Matrix", "trace"), value);
    private static Formula RealPart(Formula value) => At(Qualified("Complex", "re"), value);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(params string[] parts)
    {
        var items = new List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
            {
                items.Add(Dot);
            }
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula SetBuilder(Formula variable, Formula type, Formula predicate) =>
        Seq(OpenBrace, Typed(variable, type), Sp, Bar, Sp, predicate, CloseBrace);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        At(Qualified("ite"), condition, yes, no);
    private static Formula Sqrt(Formula value) => At(Qualified("Real", "sqrt"), value);
}
