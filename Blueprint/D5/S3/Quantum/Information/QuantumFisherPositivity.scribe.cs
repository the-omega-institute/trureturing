using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

// Escape registrations for both public declarations remain open in issue #27072.
internal sealed class QuantumFisherPositivityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/QuantumFisherPositivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-dimensional Hermitian Fisher-form quadratic forms are nonnegative.",
        H("Positivity of a finite Hermitian Fisher form"),
        Blocks(
            Paragraph(Text(
                "Fix finite parameter and state indices. A positive semidefinite complex state matrix "
                    + "rho and a Hermitian matrix L_i for every parameter i define the real Fisher-form entry "
                    + "J_ij = Re(trace(rho L_i L_j)). The theorem establishes the full real quadratic "
                    + "form directly, with no claim about infinite-dimensional or unbounded-operator models.")),
            Describe.Lean(
                DescribeId.Create("quantum-fisher-quadratic-nonneg"),
                DeclarationHandle.Create(Module + "quantum_fisher_quadratic_nonneg"),
                H("The Fisher quadratic form is nonnegative"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a real coefficient function a, the combined Hermitian matrix is the finite sum "
                            + "A = Σ_i (a_i : C) • L_i. Hermiticity of every L_i makes A Hermitian. "
                            + "The finite sum expands the displayed quadratic form to Re(trace(rho A²)).")),
                    Paragraph(Text(
                        "Cyclicity changes this to Re(trace(A rho A)). The Gram matrix A* A is positive "
                            + "semidefinite, so the positive-state trace pairing is nonnegative. This is "
                            + "the finite-dimensional bridge behind the statistical positivity clause. A "
                            + "separate coordinate-congruence application is outside this declaration.")))),
            Describe.Lean(
                DescribeId.Create("quantum-fisher-congruence-quadratic-nonneg"),
                DeclarationHandle.Create(Module + "quantum_fisher_congruence_quadratic_nonneg"),
                H("Real Jacobian congruences preserve Fisher nonnegativity"),
                StatementSource.FromAuthor(Disp(CongruenceFormula())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a real matrix T and coefficient vector b, the displayed transformed form "
                            + "is the original Fisher form evaluated at c = T.mulVec b. The first theorem "
                            + "therefore proves its nonnegativity by finite sum expansion. Since this holds "
                            + "for every coefficient vector and real Jacobian, no transformed direction has a "
                            + "negative value, so this Fisher form cannot supply a Lorentzian negative direction.")))))));

    private static Formula ResultFormula()
    {
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var iota = F.Id("iota");
        var d = F.Id("d");
        var rho = F.Id("rho");
        var a = F.Id("a");
        var L = F.Id("L");
        var i = F.Id("i");
        var j = F.Id("j");
        var matrix = Call("Matrix", d, d, complex);
        var family = Arrow(iota, matrix);
        var coeffs = Arrow(iota, real);
        var entry = QCall("Complex.re", QCall("Matrix.trace",
            new Formula.Binary(
                new Formula.Binary(rho, FormulaBinaryOperator.Multiply, At(L, i)),
                FormulaBinaryOperator.Multiply, At(L, j))));
        var summand = new Formula.Binary(
            new Formula.Binary(At(a, i), FormulaBinaryOperator.Multiply, entry),
            FormulaBinaryOperator.Multiply, At(a, j));
        var sumJ = Seq(Sum, Underscore, Grp(i, InMacro, Sp, iota), Sp,
            Seq(Sum, Underscore, Grp(j, InMacro, Sp, iota), Sp, summand));
        var hermitian = new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("i"), iota,
            QCall("Matrix.IsHermitian", At(L, i)));
        var traceOne = new Formula.Relation(QCall("Matrix.trace", rho), FormulaRelationOperator.Equal, D(1));
        var body = new Formula.Logic(
            traceOne, FormulaLogicOperator.Implies,
            new Formula.Logic(
                QCall("Matrix.PosSemidef", rho), FormulaLogicOperator.Implies,
                new Formula.Logic(
                    hermitian, FormulaLogicOperator.Implies,
                    new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, sumJ))));
        var quantified = All("rho", matrix,
            All("a", coeffs,
                All("L", family, body)));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("iota"), F.Id("Type"),
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("d"), F.Id("Type"),
                FintypeInstances(iota, FintypeInstances(d, DecidableEqInstance(d, quantified)))));
    }

    private static Formula CongruenceFormula()
    {
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var complex = Seq(Mathbb, Grp(F.Id("C")));
        var iota = F.Id("iota");
        var d = F.Id("d");
        var kappa = F.Id("kappa");
        var rho = F.Id("rho");
        var b = F.Id("b");
        var L = F.Id("L");
        var T = F.Id("T");
        var p = F.Id("p");
        var q = F.Id("q");
        var r = F.Id("r");
        var s = F.Id("s");
        var matrixD = Call("Matrix", d, d, complex);
        var family = Arrow(iota, matrixD);
        var coeffs = Arrow(kappa, real);
        var jacobian = Call("Matrix", iota, kappa, real);
        var entry = QCall("Complex.re", QCall("Matrix.trace",
            new Formula.Binary(
                new Formula.Binary(rho, FormulaBinaryOperator.Multiply, At(L, p)),
                FormulaBinaryOperator.Multiply, At(L, q))));
        var transformedEntry = new Formula.Binary(
            new Formula.Binary(At(T, p, r), FormulaBinaryOperator.Multiply, entry),
            FormulaBinaryOperator.Multiply, At(T, q, s));
        var inner = Seq(Sum, Underscore, Grp(p, InMacro, Sp, iota), Sp,
            Seq(Sum, Underscore, Grp(q, InMacro, Sp, iota), Sp, transformedEntry));
        var summand = new Formula.Binary(
            new Formula.Binary(At(b, r), FormulaBinaryOperator.Multiply, inner),
            FormulaBinaryOperator.Multiply, At(b, s));
        var outer = Seq(Sum, Underscore, Grp(r, InMacro, Sp, kappa), Sp,
            Seq(Sum, Underscore, Grp(s, InMacro, Sp, kappa), Sp, summand));
        var hermitian = new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create("p"), iota,
            QCall("Matrix.IsHermitian", At(L, p)));
        var traceOne = new Formula.Relation(QCall("Matrix.trace", rho), FormulaRelationOperator.Equal, D(1));
        var hypotheses = new Formula.Logic(
            traceOne, FormulaLogicOperator.Implies,
            new Formula.Logic(
                QCall("Matrix.PosSemidef", rho), FormulaLogicOperator.Implies,
                new Formula.Logic(
                    hermitian, FormulaLogicOperator.Implies,
                    new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, outer))));
        var quantified = All("rho", matrixD,
            All("b", coeffs,
                All("L", family,
                    All("T", jacobian, hypotheses))));
        return new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("iota"), F.Id("Type"),
            new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("d"), F.Id("Type"),
                new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("kappa"), F.Id("Type"),
                    FintypeInstances(iota,
                        FintypeInstances(d,
                            FintypeInstances(kappa, DecidableEqInstance(d, quantified)))))));
    }

    private static Formula At(Formula fn, params Formula[] args) => new Formula.Apply(fn, [.. args]);
    private static Formula Qualified(string name)
    {
        var parts = name.Split('.');
        var tokens = new System.Collections.Generic.List<Formula>();
        for (var k = 0; k < parts.Length; k++)
        {
            if (k > 0) tokens.Add(Dot);
            tokens.Add(F.Id(parts[k]));
        }
        return Seq(Operatorname, Grp([.. tokens]));
    }
    private static Formula QCall(string name, params Formula[] args) =>
        At(Qualified(name), args);
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula FintypeInstances(Formula type, Formula body) => Seq(
        OpenBracket, Call("Fintype", type), CloseBracket, Sp, body);

    private static Formula DecidableEqInstance(Formula type, Formula body) => Seq(
        OpenBracket, Call("DecidableEq", type), CloseBracket, Sp, body);
}
