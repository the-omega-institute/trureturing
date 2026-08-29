using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class FixedDepthLiClarkRecoveryDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/TestFunctions/FixedDepthLiClarkRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed-order Li-coefficient recovery controls the associated finite "
            + "Toeplitz operator and its smallest eigenvalue.",
        H("Fixed-Depth Li-Clark Recovery"),
        Blocks(Describe.Lean(
            DescribeId.Create("fixed-depth-li-clark-recovery"),
            DeclarationHandle.Create(Handle + "fixed_depth_li_clark_recovery"),
            H("Fixed-depth Li-Clark recovery"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The true and windowed Li-Clark moments are constructed from "
                        + "the supplied Li-coefficient sequences by the normalized "
                        + "second-difference formula, and the finite Toeplitz matrices "
                        + "are constructed entry by entry from those moments.")),
                Paragraph(Text(
                    "A fixed-order exponential recovery premise for every moment "
                        + "visible at depth N transfers through a finite matrix-basis "
                        + "sum to the L2 operator norm.")),
                Paragraph(Text(
                    "The Hermitian Rayleigh characterization bounds the smallest-"
                        + "eigenvalue error by the same operator norm. Exponential-"
                        + "polynomial decay then gives the displayed convergence."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula depth = F.Id("N");
        Formula coefficient = F.Id("lambda");
        Formula windowCoefficient = F.Id("lambdahat");
        Formula index = F.Id("r");
        Formula budget = F.Id("L");
        Formula row = F.Id("j");
        Formula column = F.Id("k");
        Formula moment = F.Id("c");
        Formula windowMoment = F.Id("chat");
        Formula rate = F.Id("eta");
        Formula trueMatrix = F.Id("T");
        Formula windowMatrix = F.Id("That");
        Formula trueHermitian = F.Id("hT");
        Formula windowHermitian = F.Id("hThat");
        Formula finDepth = Call("Fin", Seq(depth, Plus, D(1)));
        Formula matrixType = Call("Matrix", finDepth, finDepth, complex);

        Formula Curvature(Formula sequence, Formula r) => Div(
            Add(
                Sub(
                    Apply(sequence, Call("natAbs", Add(r, D(1)))),
                    Mul(D(2), Apply(sequence, Call("natAbs", r)))),
                Apply(sequence, Call("natAbs", Sub(r, D(1))))),
            Mul(D(2), Apply(coefficient, D(1))));

        Formula WindowSequence(Formula l) => Apply(windowCoefficient, l);
        Formula MomentAt(Formula r) => Apply(moment, r);
        Formula WindowMomentAt(Formula l, Formula r) => Apply(windowMoment, l, r);
        Formula WindowMatrixAt(Formula l) => Apply(windowMatrix, l);
        Formula Lambda(Formula variable, Formula body) =>
            Seq(Open, variable, Sp, Mapsto, Sp, body, Close);
        Formula Let(Formula name, Formula value) =>
            Seq(Operatorname, Grp(F.Id("let")), Sp, name, Sp, Eq, Sp, value);

        Formula momentDefinition = Let(moment, Lambda(index, Curvature(coefficient, index)));
        Formula windowMomentDefinition = Let(
            windowMoment,
            Lambda(budget, Lambda(index, Curvature(WindowSequence(budget), index))));
        Formula rateDefinition = Let(
            rate,
            Lambda(
                budget,
                Mul(
                    Call("exp", Seq(Minus, budget)),
                    Seq(budget, Caret, Grp(depth, Minus, D(1))))));
        Formula matrixDomain = Seq(
            row, Comma, column, InMacro, Call("Fin", Seq(depth, Plus, D(1))));
        Formula trueMatrixDefinition = Let(
            trueMatrix,
            Call("Matrix", Lambda(matrixDomain, MomentAt(Sub(row, column)))));
        Formula windowMatrixDefinition = Let(
            windowMatrix,
            Lambda(
                budget,
                Call("Matrix", Lambda(
                    matrixDomain,
                    WindowMomentAt(budget, Sub(row, column))))));
        Formula trueHermitianDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, trueHermitian, Sp, Eq, Sp,
            Call("curvatureHermitian", coefficient), Colon, Sp,
            Call("IsHermitian", trueMatrix));
        Formula windowHermitianDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp, windowHermitian, Sp, Eq, Sp,
            Lambda(budget, Call("curvatureHermitian", WindowSequence(budget))),
            Colon, Sp,
            new Formula.BindMany(
                FormulaQuantifier.ForAll,
                [new Formula.BoundVariable(FormulaIdentifier.Create("L"), real)],
                Call("IsHermitian", WindowMatrixAt(budget))));
        Formula recoveryPremise = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("r"), integer)],
            Implies(
                LessEqual(Call("natAbs", index), depth),
                Call(
                    "IsBigOAtTop",
                    Lambda(
                        budget,
                        Sub(MomentAt(index), WindowMomentAt(budget, index))),
                    rate)));
        Formula operatorRecovery = Call(
            "IsBigOAtTop",
            Lambda(
                budget,
                Call("opNorm", Sub(trueMatrix, WindowMatrixAt(budget)))),
            rate);
        Formula trueFloor = Call("lambdaMin", trueMatrix, trueHermitian);
        Formula windowFloor = Call(
            "lambdaMin",
            WindowMatrixAt(budget),
            Apply(windowHermitian, budget));
        Formula floorRecovery = Call(
            "IsBigOAtTop",
            Lambda(budget, Sub(windowFloor, trueFloor)),
            rate);
        Formula floorConvergence = Call(
            "TendstoAtTop",
            Lambda(budget, windowFloor),
            trueFloor);

        Formula premise = All(
            momentDefinition,
            windowMomentDefinition,
            rateDefinition,
            recoveryPremise,
            trueMatrixDefinition,
            windowMatrixDefinition,
            trueHermitianDefinition,
            windowHermitianDefinition);
        Formula conclusion = All(operatorRecovery, floorRecovery, floorConvergence);

        return Disp(ForAll(
            [
                Bound("N", nat),
                Bound("lambda", Arrow(nat, real)),
                Bound("lambdahat", Arrow(real, Arrow(nat, real))),
            ],
            Implies(premise, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula ForAll(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
