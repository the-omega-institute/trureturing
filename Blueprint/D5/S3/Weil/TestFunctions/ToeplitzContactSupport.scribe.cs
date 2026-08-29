using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class ToeplitzContactSupportDocument : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Weil/TestFunctions/ToeplitzContactSupport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A contact eigenvector localizes a Toeplitz residual on finitely many polynomial zeros.",
        H("Toeplitz Contact Support"),
        Blocks(Describe.Lean(
            DescribeId.Create("toeplitz-contact-support"),
            DeclarationHandle.Create(Handle + "toeplitz_contact_support"),
            H("Toeplitz contact support"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The Fourier moments, Toeplitz matrix, and analytic contact "
                        + "polynomial are constructed from the supplied completion "
                        + "measure and coefficient vector.")),
                Paragraph(Text(
                    "Normalized-Haar monomial orthogonality turns the contact "
                        + "eigenvector equation into a zero residual quadratic integral. "
                        + "The residual support is therefore contained in the contact "
                        + "zero set.")),
                Paragraph(Text(
                    "The polynomial is nonzero because the coefficient vector is unit. "
                        + "Its circle roots are finite, have cardinality at most its "
                        + "degree, and enumerate both the residual Dirac sum and the "
                        + "full optimizer decomposition."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula integer = Seq(Mathbb, Grp(F.Id("Z")));
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula nonnegativeReal = Call("NonnegativeReal");
        Formula extendedNonnegativeReal = Call("ExtendedNonnegativeReal");
        Formula circle = Call("Circle");
        Formula finiteMeasure = Call("FiniteMeasure", circle);
        Formula depth = F.Id("N");
        Formula completion = F.Id("mu");
        Formula residual = F.Id("sigma");
        Formula alpha = F.Id("alpha");
        Formula vector = F.Id("v");
        Formula moment = F.Id("m");
        Formula toeplitz = F.Id("T");
        Formula contactPolynomial = F.Id("q");
        Formula row = F.Id("j");
        Formula column = F.Id("k");
        Formula exponent = F.Id("ell");
        Formula circlePoint = F.Id("z");
        Formula atomCount = F.Id("M");
        Formula atom = F.Id("r");
        Formula point = F.Id("point");
        Formula weight = F.Id("weight");
        Formula finDepth = Call("Fin", Add(depth, D(1)));
        Formula finAtoms = Call("Fin", atomCount);
        Formula vectorType = Arrow(finDepth, complex);

        Formula Lambda(Formula variable, Formula body) =>
            Seq(Open, variable, Sp, Mapsto, Sp, body, Close);
        Formula Let(Formula name, Formula value) =>
            Seq(Operatorname, Grp(F.Id("let")), Sp, name, Sp, Eq, Sp, value);
        Formula AtomicSum() => Call(
            "sum",
            atom,
            finAtoms,
            Call("smul", Apply(weight, atom), Call("dirac", Apply(point, atom))));

        Formula decomposition = Equal(
            completion,
            Add(Call("smul", alpha, Call("normalizedCircleHaar")), residual));
        Formula momentDefinition = Let(
            moment,
            Lambda(
                Seq(exponent, Colon, integer),
                Call(
                    "integral",
                    circlePoint,
                    circle,
                    Call("zpow", circlePoint, Call("neg", exponent)),
                    completion)));
        Formula toeplitzDefinition = Let(
            toeplitz,
            Call(
                "Matrix",
                Lambda(
                    Seq(row, Comma, column, InMacro, finDepth),
                    Apply(moment, Sub(row, column)))));
        Formula polynomialDefinition = Let(
            contactPolynomial,
            Call(
                "sum",
                row,
                finDepth,
                Call("monomial", Apply(vector, row), row)));
        Formula unitVector = Equal(
            Call("dotProduct", Call("star", vector), vector),
            D(1));
        Formula eigenvector = Equal(
            Call("mulVec", toeplitz, vector),
            Call("smul", Call("toComplex", alpha), vector));
        Formula zeroSet = new Formula.SetBuilder(
            Equal(Call("eval", contactPolynomial, circlePoint), D(0)),
            circlePoint,
            circle);
        Formula supportClause = new Formula.Relation(
            Call("support", residual),
            FormulaRelationOperator.SubsetOf,
            zeroSet);
        Formula degreeBound = LessEqual(
            Call("natDegree", contactPolynomial),
            depth);
        Formula pointRoot = ForAll(
            [Bound("r", finAtoms)],
            Equal(
                Call("eval", contactPolynomial, Apply(point, atom)),
                D(0)));
        Formula finiteWeight = ForAll(
            [Bound("r", finAtoms)],
            NotEqual(Apply(weight, atom), Call("infinity")));
        Formula atomicResidual = Equal(residual, AtomicSum());
        Formula atomicCompletion = Equal(
            completion,
            Add(Call("smul", alpha, Call("normalizedCircleHaar")), AtomicSum()));
        Formula atomicWitness = Exists(
            [
                Bound("M", natural),
                Bound("point", Arrow(finAtoms, circle)),
                Bound("weight", Arrow(finAtoms, extendedNonnegativeReal)),
            ],
            All(
                LessEqual(atomCount, Call("natDegree", contactPolynomial)),
                pointRoot,
                finiteWeight,
                atomicResidual,
                atomicCompletion));
        Formula premise = All(
            decomposition,
            momentDefinition,
            toeplitzDefinition,
            polynomialDefinition,
            unitVector,
            eigenvector);
        Formula conclusion = All(supportClause, degreeBound, atomicWitness);

        return Disp(ForAll(
            [
                Bound("N", natural),
                Bound("mu", finiteMeasure),
                Bound("sigma", finiteMeasure),
                Bound("alpha", nonnegativeReal),
                Bound("v", vectorType),
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

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

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

    private static Formula Exists(
        Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
}
