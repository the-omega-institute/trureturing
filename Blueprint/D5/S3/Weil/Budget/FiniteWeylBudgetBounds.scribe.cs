using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class FiniteWeylBudgetBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Budget/FiniteWeylBudgetBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite parity pencils converge monotonically to the full generalized "
            + "Rayleigh budget interval.",
        H("Finite Weyl Budget Bounds"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-weyl-budget-bounds"),
            DeclarationHandle.Create(Prefix + "finite_weyl_budget_bounds"),
            H("Finite Hermitian pencils bound and approximate the full budget interval"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The displayed statement constructs both finite quotient families, "
                        + "their endpoints, the two rank-one pencils, and finite feasibility "
                        + "directly from the matrix and boundary data.")),
                Paragraph(Text(
                    "Kernel positivity handles zero boundary pairings. Nested finite quotient "
                        + "sets and one-sided approximation of every full quotient express the "
                        + "Galerkin density hypothesis without assuming endpoint convergence.")),
                Paragraph(Text(
                    "Each finite pencil is positive semidefinite exactly on its corresponding "
                        + "budget ray. The lower endpoints increase, the upper endpoints "
                        + "decrease, both converge to the full interval, and a crossed finite "
                        + "interval supplies incompatible lower and upper requirements."))),
            DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula value) =>
        Call("apply", function, value);

    private static Formula ApplyTwo(Formula function, Formula first, Formula second) =>
        Call("applyTwo", function, first, second);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula Lambda(string name, Formula domain, Formula body) =>
        Seq(F.Id(name), Colon, Sp, domain, Sp, Mapsto, Sp, body);

    private static Formula Let(string name, Formula value) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, F.Id(name), Sp, Eq, Sp, value, Comma, Sp);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type"), prop = F.Id("Prop");
        Formula natural = Call("Nat"), real = Call("Real"), complex = Call("Complex");
        Formula evenTest = F.Id("EvenTest"), oddTest = F.Id("OddTest");
        Formula evenDim = F.Id("evenDim"), oddDim = F.Id("oddDim");
        Formula evenBase = F.Id("evenBase"), oddBase = F.Id("oddBase");
        Formula evenBoundary = F.Id("evenBoundary"), oddBoundary = F.Id("oddBoundary");
        Formula fullEvenBase = F.Id("fullEvenBase");
        Formula fullEvenBoundary = F.Id("fullEvenBoundary");
        Formula fullOddBase = F.Id("fullOddBase");
        Formula fullOddBoundary = F.Id("fullOddBoundary");
        Formula reference = F.Id("referenceBudget");
        Formula n = F.Id("N"), r = F.Id("R"), q = F.Id("q");
        Formula epsilon = F.Id("epsilon"), qn = F.Id("qN");
        Formula x = F.Id("x");
        Formula finiteEven = F.Id("finiteEvenQuotients");
        Formula finiteOdd = F.Id("finiteOddQuotients");
        Formula fullEven = F.Id("fullEvenQuotients");
        Formula fullOdd = F.Id("fullOddQuotients");
        Formula finiteLower = F.Id("finiteLower"), finiteUpper = F.Id("finiteUpper");
        Formula fullLower = F.Id("fullLower"), fullUpper = F.Id("fullUpper");
        Formula evenPencil = F.Id("evenPencil"), oddPencil = F.Id("oddPencil");
        Formula feasible = F.Id("feasible");

        Formula Dim(Formula family, Formula index) => Apply(family, index);
        Formula FiniteVector(Formula family, Formula index) =>
            new Formula.TypeArrow(Call("Fin", Dim(family, index)), complex);
        Formula FiniteMatrix(Formula family, Formula index)
        {
            Formula coordinate = Call("Fin", Dim(family, index));
            return Call("Matrix", coordinate, coordinate, complex);
        }
        Formula BaseAt(Formula family, Formula index) => Apply(family, index);
        Formula BoundaryAt(Formula family, Formula index) => Apply(family, index);
        Formula Pairing(Formula boundary, Formula vector) =>
            Call("dot", Call("star", boundary), vector);
        Formula Quadratic(Formula matrix, Formula vector) =>
            Call("Re", Call("dot", Call("star", vector), Call("mulVec", matrix, vector)));
        Formula NormSquare(Formula value) => Call("normSq", value);
        Formula In(Formula value, Formula set) => Call("Mem", value, set);
        Formula SetAt(Formula family, Formula index) => Apply(family, index);
        Formula EndpointAt(Formula endpoint, Formula index) => Apply(endpoint, index);
        Formula PencilAt(Formula pencil, Formula index, Formula budget) =>
            ApplyTwo(pencil, index, budget);

        Formula evenVector = FiniteVector(evenDim, n);
        Formula oddVector = FiniteVector(oddDim, n);
        Formula evenMatrix = FiniteMatrix(evenDim, n);
        Formula oddMatrix = FiniteMatrix(oddDim, n);
        Formula finiteEvenPairing = Pairing(BoundaryAt(evenBoundary, n), x);
        Formula finiteOddPairing = Pairing(BoundaryAt(oddBoundary, n), x);
        Formula finiteEvenRayleigh = Call(
            "div",
            Call("neg", Quadratic(BaseAt(evenBase, n), x)),
            NormSquare(finiteEvenPairing));
        Formula finiteOddRayleigh = Call(
            "div",
            Quadratic(BaseAt(oddBase, n), x),
            NormSquare(finiteOddPairing));
        Formula finiteEvenSet = new Formula.SetBuilder(
            Exists(
                [Bound("x", evenVector)],
                And(NotEqual(finiteEvenPairing, D(0)), Equal(q, finiteEvenRayleigh))),
            q,
            real);
        Formula finiteOddSet = new Formula.SetBuilder(
            Exists(
                [Bound("x", oddVector)],
                And(NotEqual(finiteOddPairing, D(0)), Equal(q, finiteOddRayleigh))),
            q,
            real);
        Formula fullEvenValue = Apply(fullEvenBoundary, x);
        Formula fullOddValue = Apply(fullOddBoundary, x);
        Formula fullEvenSet = new Formula.SetBuilder(
            Exists(
                [Bound("x", evenTest)],
                And(
                    NotEqual(fullEvenValue, D(0)),
                    Equal(q, Call(
                        "div", Call("neg", Apply(fullEvenBase, x)),
                        NormSquare(fullEvenValue))))),
            q,
            real);
        Formula fullOddSet = new Formula.SetBuilder(
            Exists(
                [Bound("x", oddTest)],
                And(
                    NotEqual(fullOddValue, D(0)),
                    Equal(q, Call(
                        "div", Apply(fullOddBase, x), NormSquare(fullOddValue))))),
            q,
            real);

        Formula evenRankOne = Call(
            "vecMulVec", BoundaryAt(evenBoundary, n),
            Call("star", BoundaryAt(evenBoundary, n)));
        Formula oddRankOne = Call(
            "vecMulVec", BoundaryAt(oddBoundary, n),
            Call("star", BoundaryAt(oddBoundary, n)));
        Formula shift = Call("ofReal", Call("sub", r, reference));
        Formula evenPencilValue = Call(
            "add", BaseAt(evenBase, n), Call("smul", shift, evenRankOne));
        Formula oddPencilValue = Call(
            "sub", BaseAt(oddBase, n), Call("smul", shift, oddRankOne));

        Formula definitions = Seq(
            Let("finiteEvenQuotients", Lambda("N", natural, finiteEvenSet)),
            Let("finiteOddQuotients", Lambda("N", natural, finiteOddSet)),
            Let("fullEvenQuotients", fullEvenSet),
            Let("fullOddQuotients", fullOddSet),
            Let("finiteLower", Lambda(
                "N", natural, Call("add", reference, Call("sSup", SetAt(finiteEven, n))))),
            Let("finiteUpper", Lambda(
                "N", natural, Call("add", reference, Call("sInf", SetAt(finiteOdd, n))))),
            Let("fullLower", Call("add", reference, Call("sSup", fullEven))),
            Let("fullUpper", Call("add", reference, Call("sInf", fullOdd))),
            Let("evenPencil", Seq(
                n, Colon, Sp, natural, Comma, Sp, r, Colon, Sp, real,
                Sp, Mapsto, Sp, evenPencilValue)),
            Let("oddPencil", Seq(
                n, Colon, Sp, natural, Comma, Sp, r, Colon, Sp, real,
                Sp, Mapsto, Sp, oddPencilValue)),
            Let("feasible", Seq(
                n, Colon, Sp, natural, Comma, Sp, r, Colon, Sp, real,
                Sp, Mapsto, Sp,
                And(
                    Call("PosSemidef", PencilAt(evenPencil, n, r)),
                    Call("PosSemidef", PencilAt(oddPencil, n, r))))),
            Implies(Assumptions(), Conclusions()));

        Formula Assumptions()
        {
            Formula evenKernel = ForAll(
                [Bound("N", natural), Bound("x", evenVector)],
                Implies(
                    Equal(finiteEvenPairing, D(0)),
                    AtMost(D(0), Quadratic(BaseAt(evenBase, n), x))));
            Formula oddKernel = ForAll(
                [Bound("N", natural), Bound("x", oddVector)],
                Implies(
                    Equal(finiteOddPairing, D(0)),
                    AtMost(D(0), Quadratic(BaseAt(oddBase, n), x))));
            Formula evenApproximation = ForAll(
                [Bound("q", real), Bound("epsilon", real)],
                Implies(
                    And(In(q, fullEven), Less(D(0), epsilon)),
                    Exists(
                        [Bound("N", natural), Bound("qN", real)],
                        And(
                            In(qn, SetAt(finiteEven, n)),
                            Less(Call("sub", q, epsilon), qn)))));
            Formula oddApproximation = ForAll(
                [Bound("q", real), Bound("epsilon", real)],
                Implies(
                    And(In(q, fullOdd), Less(D(0), epsilon)),
                    Exists(
                        [Bound("N", natural), Bound("qN", real)],
                        And(
                            In(qn, SetAt(finiteOdd, n)),
                            Less(qn, Call("add", q, epsilon))))));

            return All(
                ForAll([Bound("N", natural)],
                    Call("IsHermitian", BaseAt(evenBase, n))),
                ForAll([Bound("N", natural)],
                    Call("IsHermitian", BaseAt(oddBase, n))),
                evenKernel,
                oddKernel,
                ForAll([Bound("N", natural)], Exists(
                    [Bound("x", evenVector)], NotEqual(finiteEvenPairing, D(0)))),
                ForAll([Bound("N", natural)], Exists(
                    [Bound("x", oddVector)], NotEqual(finiteOddPairing, D(0)))),
                ForAll([Bound("N", natural)],
                    Call("BddAbove", SetAt(finiteEven, n))),
                ForAll([Bound("N", natural)],
                    Call("BddBelow", SetAt(finiteOdd, n))),
                Exists([Bound("x", evenTest)], NotEqual(Apply(fullEvenBoundary, x), D(0))),
                Exists([Bound("x", oddTest)], NotEqual(Apply(fullOddBoundary, x), D(0))),
                Call("BddAbove", fullEven),
                Call("BddBelow", fullOdd),
                ForAll([Bound("N", natural)], Call(
                    "Subset", SetAt(finiteEven, n),
                    SetAt(finiteEven, Call("add", n, D(1))))),
                ForAll([Bound("N", natural)], Call(
                    "Subset", SetAt(finiteOdd, n),
                    SetAt(finiteOdd, Call("add", n, D(1))))),
                ForAll([Bound("N", natural)],
                    Call("Subset", SetAt(finiteEven, n), fullEven)),
                ForAll([Bound("N", natural)],
                    Call("Subset", SetAt(finiteOdd, n), fullOdd)),
                evenApproximation,
                oddApproximation);
        }

        Formula Conclusions()
        {
            Formula hermitianPencils = ForAll(
                [Bound("N", natural), Bound("R", real)],
                And(
                    Call("IsHermitian", PencilAt(evenPencil, n, r)),
                    Call("IsHermitian", PencilAt(oddPencil, n, r))));
            Formula evenEndpoint = ForAll(
                [Bound("N", natural), Bound("R", real)],
                Call(
                    "Iff",
                    Call("PosSemidef", PencilAt(evenPencil, n, r)),
                    AtMost(EndpointAt(finiteLower, n), r)));
            Formula oddEndpoint = ForAll(
                [Bound("N", natural), Bound("R", real)],
                Call(
                    "Iff",
                    Call("PosSemidef", PencilAt(oddPencil, n, r)),
                    AtMost(r, EndpointAt(finiteUpper, n))));
            Formula interval = ForAll(
                [Bound("N", natural), Bound("R", real)],
                Call(
                    "Iff",
                    ApplyTwo(feasible, n, r),
                    Call(
                        "MemIcc", r, EndpointAt(finiteLower, n),
                        EndpointAt(finiteUpper, n))));
            Formula evenRequirement = ForAll(
                [Bound("R", real)],
                Implies(
                    Call("PosSemidef", PencilAt(evenPencil, n, r)),
                    AtMost(EndpointAt(finiteLower, n), r)));
            Formula oddRequirement = ForAll(
                [Bound("R", real)],
                Implies(
                    Call("PosSemidef", PencilAt(oddPencil, n, r)),
                    AtMost(r, EndpointAt(finiteUpper, n))));
            Formula noFeasible = Call(
                "Not", Exists([Bound("R", real)], ApplyTwo(feasible, n, r)));
            Formula certificate = ForAll(
                [Bound("N", natural)],
                Implies(
                    Less(EndpointAt(finiteUpper, n), EndpointAt(finiteLower, n)),
                    All(evenRequirement, oddRequirement, noFeasible)));

            return All(
                hermitianPencils,
                evenEndpoint,
                oddEndpoint,
                Call("Monotone", finiteLower),
                Call("Antitone", finiteUpper),
                Call("Tendsto", finiteLower, F.Id("atTop"), Call("nhds", fullLower)),
                Call("Tendsto", finiteUpper, F.Id("atTop"), Call("nhds", fullUpper)),
                interval,
                certificate);
        }

        return F.Disp(ForAll(
            [
                Bound("EvenTest", type),
                Bound("OddTest", type),
                Bound("evenDim", new Formula.TypeArrow(natural, natural)),
                Bound("oddDim", new Formula.TypeArrow(natural, natural)),
                Bound("evenBase", Call(
                    "DependentMap", Seq(n, Colon, Sp, natural), evenMatrix)),
                Bound("oddBase", Call(
                    "DependentMap", Seq(n, Colon, Sp, natural), oddMatrix)),
                Bound("evenBoundary", Call(
                    "DependentMap", Seq(n, Colon, Sp, natural), evenVector)),
                Bound("oddBoundary", Call(
                    "DependentMap", Seq(n, Colon, Sp, natural), oddVector)),
                Bound("fullEvenBase", new Formula.TypeArrow(evenTest, real)),
                Bound("fullEvenBoundary", new Formula.TypeArrow(evenTest, complex)),
                Bound("fullOddBase", new Formula.TypeArrow(oddTest, real)),
                Bound("fullOddBoundary", new Formula.TypeArrow(oddTest, complex)),
                Bound("referenceBudget", real),
            ],
            definitions));
    }
}
