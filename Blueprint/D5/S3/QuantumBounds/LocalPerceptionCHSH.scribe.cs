using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class LocalPerceptionCHSHDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/LocalPerceptionCHSH.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/ray2025localperception");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The termwise local-perception CHSH sum has sharp upper bound two for all two-qubit states and dichotomic settings.",
        H("The sharp local-perception CHSH bound"),
        Blocks(
            Node("is-dichotomic", "Dichotomic observables", "IsDichotomic", DichotomicFormula(),
                "The dichotomic positive-operator-valued measurement condition is positivity of both identity plus A and identity minus A. Dividing these matrices by two gives the effects for the two outcomes. Matrix.PosSemidef includes Hermiticity over the complex numbers, so this condition describes Hermitian contractions and includes projective observables with outcomes plus and minus one.",
                AssessedProvenance.FromLiterature(Source)),
            Node("mean-a", "Alice's local mean", "meanA", MeanFormula(true),
                "Equations (5) and (10) give Alice's mean as the trace against her reduced state. Equivalently, it is the real part of Matrix.trace of the bipartite state times the Kronecker product of Alice's observable with the identity on Bob's factor.",
                AssessedProvenance.FromLiterature(Source)),
            Node("mean-b", "Bob's local mean", "meanB", MeanFormula(false),
                "Equations (5) and (10) give Bob's mean as the trace against his reduced state. Equivalently, it is the real part of Matrix.trace of the bipartite state times the Kronecker product of the identity on Alice's factor with Bob's observable.",
                AssessedProvenance.FromLiterature(Source)),
            Node("correl", "The bipartite correlator", "correl", CorrelFormula(),
                "Equation (11) gives the correlator as the trace of the state times the Kronecker product of the two observables. Taking Complex.re defines a real number for every complex matrix; for a density matrix and Hermitian observables, the trace is already real.",
                AssessedProvenance.FromLiterature(Source)),
            Node("chsh-coeff", "The CHSH coefficient table", "chshCoeff", CoeffFormula(),
                "Equation (19) uses two settings on each side. The coefficient is one for the first three pairs and minus one when both settings have index one. The marginal coefficients vanish.",
                AssessedProvenance.FromLiterature(Source)),
            Node("lpo-chsh", "The termwise local-perception sum", "lpoCHSH", SumFormula(),
                "This is the termwise sum in the second line of Equation (21), with the CHSH coefficients of Equation (19). Equation (35) identifies each local-perception correlator with the product of the two local means and the ordinary correlator, so summing these correlators with the CHSH coefficients gives the same expression. The bound concerns this termwise functional. The first line of Equation (21), the expectation of the tensor product of the two perceived Bell operators, contains cross terms between different settings and gives four for the state |00⟩ with σ_z at every setting.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The bound two is attained", "claim", ClaimFormula(),
                "The conjecture after Equation (31) asks whether the upper bound two persists for arbitrary settings. The first clause states the bound for every positive-semidefinite two-qubit state of trace one and every pair of dichotomic settings on each side, without an orthogonality assumption. The second clause states that some such state and settings attain two. Together they say that the largest termwise value over all states and settings is exactly two.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("local-perception-chsh-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The sharp bound holds for all settings"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "For outcome signs epsilon and eta equal to plus or minus one, the local effects are (1 + epsilon A)/2 and (1 + eta B)/2. Their Kronecker product is positive semidefinite. Its expectation in a positive-semidefinite state of trace one is nonnegative and expands to (1 + epsilon a + eta b + epsilon eta C)/4.")),
                    Paragraph(Text(
                        "Relabeling either local outcome changes the signs of its mean and the corresponding correlators, preserving every product of the two means and the correlator. Thus the four means p, q, r, s may be taken in the interval from zero to one. The positivity inequalities give C00 at most one, C01 at most 1 - p + s, C10 at most 1 + q - r, and C11 at least q + s - 1. Multiplication by the nonnegative local means bounds the sum by G = pr + ps(1 - p + s) + qr(1 + q - r) + qs(1 - q - s).")),
                    Paragraph(Text(
                        "The polynomial identity 2 - G = ((1 - p)/2)(r + s² + (1 - s)²) + s(1 - p)² + ((1 - r)/2)(p + q² + (1 - q)²) + q(1 - r)² + (1 - q)(1 - s)(1 + q + s) expresses the difference as a sum of nonnegative terms. This proves the upper bound two. The state |00⟩⟨00| with σ_z at every setting has all means and correlators equal to one, so its termwise sum is two and attains the bound."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("ray-2025-local-perception-chsh-bound"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("local-perception-chsh-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "QuantumBounds", "LocalPerceptionCHSH", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(F.Open, value, F.Close);
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
    private static Formula FinTwo() => At(Qualified("Fin"), D(2));
    private static Formula PairIndex() => Parenthesized(Seq(FinTwo(), Sp, Times, Sp, FinTwo()));
    private static Formula MatrixType() => At(Qualified("Matrix"), FinTwo(), FinTwo(), Complexes());
    private static Formula StateType() => At(Qualified("Matrix"), PairIndex(), PairIndex(), Complexes());
    private static Formula SettingsType() => Parenthesized(new Formula.TypeArrow(FinTwo(), MatrixType()));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Some(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula ImpliesFormula(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Trace(Formula matrix) => At(Qualified("Matrix", "trace"), matrix);
    private static Formula RealPart(Formula value) => At(Qualified("Complex", "re"), value);
    private static Formula PositiveSemidefinite(Formula matrix) => At(Qualified("Matrix", "PosSemidef"), matrix);
    private static Formula Kronecker(Formula left, Formula right) => At(Qualified("Matrix", "kronecker"), left, right);
    private static Formula SumOver(string variable, Formula summand) => Seq(
        new Formula.Subscript(Sum, Seq(X(variable), Colon, Sp, FinTwo())), Sp, Parenthesized(summand));

    private static Formula DichotomicFormula() => All("A", MatrixType(),
        Equivalent(LocalCall("IsDichotomic", X("A")), And(
            PositiveSemidefinite(Parenthesized(Add(D(1), X("A")))),
            PositiveSemidefinite(Parenthesized(Subtract(D(1), X("A")))))));

    private static Formula MeanFormula(bool alice)
    {
        var observable = alice ? "A" : "B";
        var tensor = alice ? Kronecker(X(observable), D(1)) : Kronecker(D(1), X(observable));
        return All("rho", StateType(), All(observable, MatrixType(), Equal(
            LocalCall(alice ? "meanA" : "meanB", X("rho"), X(observable)),
            RealPart(Trace(Multiply(X("rho"), tensor))))));
    }

    private static Formula CorrelFormula() => All("rho", StateType(), All("A", MatrixType(),
        All("B", MatrixType(), Equal(LocalCall("correl", X("rho"), X("A"), X("B")),
            RealPart(Trace(Multiply(X("rho"), Kronecker(X("A"), X("B")))))))));

    private static Formula CoeffFormula() => Equal(Local("chshCoeff"), Seq(
        OpenBracket, OpenBracket, D(1), Comma, Sp, D(1), CloseBracket, Comma, Sp,
        OpenBracket, D(1), Comma, Sp, new Formula.Negate(D(1)), CloseBracket, CloseBracket));

    private static Formula SumFormula()
    {
        Formula summand = Multiply(Multiply(Multiply(LocalCall("chshCoeff", X("x"), X("y")),
            LocalCall("meanA", X("rho"), At(X("A"), X("x")))),
            LocalCall("meanB", X("rho"), At(X("B"), X("y")))),
            LocalCall("correl", X("rho"), At(X("A"), X("x")), At(X("B"), X("y"))));
        return All("rho", StateType(), All("A", SettingsType(), All("B", SettingsType(),
            Equal(LocalCall("lpoCHSH", X("rho"), X("A"), X("B")),
                SumOver("x", SumOver("y", summand))))));
    }

    private static Formula DichotomicSettings(string variable, string family) =>
        All(variable, FinTwo(), LocalCall("IsDichotomic", At(X(family), X(variable))));

    private static Formula ClaimFormula()
    {
        Formula upperBound = All("rho", StateType(),
            ImpliesFormula(PositiveSemidefinite(X("rho")),
                ImpliesFormula(Equal(Trace(X("rho")), D(1)),
                    All("A", SettingsType(), All("B", SettingsType(),
                        ImpliesFormula(DichotomicSettings("x", "A"),
                            ImpliesFormula(DichotomicSettings("y", "B"),
                                AtMost(LocalCall("lpoCHSH", X("rho"), X("A"), X("B")), D(2)))))))));
        Formula attainment = Some("rho", StateType(), Some("A", SettingsType(), Some("B", SettingsType(),
            And(PositiveSemidefinite(X("rho")), And(Equal(Trace(X("rho")), D(1)),
                And(DichotomicSettings("x", "A"), And(DichotomicSettings("y", "B"),
                    Equal(LocalCall("lpoCHSH", X("rho"), X("A"), X("B")), D(2)))))))));
        return Equivalent(Local("claim"), And(upperBound, attainment));
    }
}
