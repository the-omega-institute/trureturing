using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class FiniteKrausChannelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Kraus realizations in the canonical completely positive channel interface.",
        H("Finite Kraus Quantum Channels"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-kraus-canonical-channel"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Foundation/FiniteKrausChannel.finite_kraus_quantum_channel"),
            H("Kraus completeness gives a canonical quantum channel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A, B and R are arbitrary finite coordinate types, including empty types. "
                    + "K(r) is a complex matrix from A to B. The sole matrix hypothesis is "
                    + "the displayed completeness identity.")),
                Paragraph(Text(
                    "QuantumChannel is the canonical FiniteStateChannel bundle: a Mathlib "
                    + "CompletelyPositiveMap on CStarMatrix, positive at every finite amplification, "
                    + "together with trace preservation for every matrix. The functions toCstar "
                    + "and fromCstar are CStarMatrix.ofMatrix and its inverse. Adjoint means "
                    + "conjugate transpose. The displayed action holds for every input matrix.")),
                Paragraph(Text(
                    "The proof closure retains Alex Meiburg's Physlib Kraus complete "
                    + "positivity and trace preservation proofs from revision "
                    + "6a09b2d1761a0d4430083045a247eb121d8da260, under the full Apache 2.0 "
                    + "license retained in the Lean source. A star algebra coordinate equivalence "
                    + "transports its Kronecker amplification to canonical CStarMatrix amplification. "
                    + "The retained closure retires when equivalent declarations enter pinned Mathlib. "
                    + "The concrete shifted-record realization consumes this bridge."))),
            DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-kraus-trace-preserving"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteKrausChannel.IsTracePreserving"),
                H("Trace preservation on every matrix"),
                StatementSource.FromAuthor(TracePreservingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A matrix map is trace preserving when its output has the same trace as its input for every matrix over the semiring."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-kraus-trace-completeness"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteKrausChannel.of_kraus_isTracePreserving"),
                H("Kraus completeness gives trace preservation"),
                StatementSource.FromAuthor(KrausTracePreservingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Over a commutative semiring with a star operation, the completeness identity for two finite Kraus families makes their matrix map preserve the trace of every input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-kraus-add-kron"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteKrausChannel.add_kron"),
                H("Kronecker amplification distributes over addition"),
                StatementSource.FromAuthor(AddKronFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("MatrixMap.kron is additive in its first matrix map over a commutative semiring. The finite coordinate types A, B, C and D may be empty. This identity gives the addition closure of MatrixMap.IsCompletelyPositive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-kraus-cp-add"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteKrausChannel.add"),
                H("Completely positive maps are closed under addition"),
                StatementSource.FromAuthor(AddCpFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite A and B and an RCLike scalar R, the sum of two completely positive matrix maps is completely positive. At every finite amplification, add_kron expresses the image as the sum of two positive semidefinite images. IptPptSquaredEquivalence.gamma_cp uses this closure to combine the four branches of the flag lift."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-kraus-conjugation"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteKrausChannel.conj"),
                H("Conjugation as a linear matrix map"),
                StatementSource.FromAuthor(ConjFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite input coordinate type A and an RCLike scalar R, MatrixMap.conj y is the linear map sending x to y x y adjoint, with arbitrary output coordinate type B."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-kraus-conjugation-apply"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/FiniteKrausChannel.conj_apply"),
                H("Evaluation of matrix conjugation"),
                StatementSource.FromAuthor(ConjFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluating MatrixMap.conj y at x gives y x y adjoint for every matrix x on the finite input coordinate type."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Eqn(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Conj(Formula a) => Seq(a, Caret, Grp(Star));
    private static Formula All(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Apply(Formula head, params Formula[] args) => new Formula.Apply(head, [.. args]);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Instance(string cls, Formula arg) =>
        Seq(OpenBracket, Call(cls, arg), CloseBracket, Sp);
    private static Formula MatrixMapOf(Formula a, Formula b, Formula r) => Call("MatrixMap", a, b, r);
    private static Formula TracePreservingFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), r = F.Id("R"), m = F.Id("M"), x = F.Id("x");
        Formula preservation = All([Bound("x", Call("Matrix", a, a, r))],
            Eqn(Call("trace", Apply(m, x)), Call("trace", x)));
        Formula statement = new Formula.Logic(
            Apply(Qualified("MatrixMap", "IsTracePreserving"), m),
            FormulaLogicOperator.Iff, preservation);
        return Disp(All([Bound("A", Named("Type")), Bound("B", Named("Type")),
            Bound("R", Named("Type"))],
            Seq(Instance("Fintype", a), Instance("Fintype", b), Instance("Semiring", r),
                All([Bound("M", MatrixMapOf(a, b, r))], statement))));
    }

    private static Formula KrausTracePreservingFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), s = F.Id("S"), kappa = F.Id("Kappa");
        Formula m = F.Id("M"), n = F.Id("N"), k = F.Id("k");
        Formula family = new Formula.TypeArrow(kappa, Call("Matrix", b, a, s));
        Formula completeness = Eqn(Seq(Sum, Underscore, Grp(k, InMacro, kappa), Sp,
            Mul(Call("conjTranspose", Apply(n, k)), Apply(m, k))), Num(1));
        Formula preservation = Apply(Qualified("MatrixMap", "IsTracePreserving"),
            Apply(Seq(Named("MatrixMap"), Dot, Named("of"), Underscore, Grp(Named("kraus"))), m, n));
        return Disp(All([Bound("A", Named("Type")), Bound("B", Named("Type")),
            Bound("S", Named("Type")), Bound("Kappa", Named("Type"))],
            Seq(Instance("Fintype", a), Instance("DecidableEq", a),
                Instance("Fintype", b), Instance("Fintype", kappa),
                Instance("CommSemiring", s), Instance("Star", s),
                All([Bound("M", family), Bound("N", family)],
                    new Formula.Logic(completeness, FormulaLogicOperator.Implies, preservation)))));
    }

    private static Formula ConjFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), r = F.Id("R");
        Formula x = F.Id("x"), y = F.Id("y");
        Formula statement = All([Bound("y", Call("Matrix", b, a, r)),
            Bound("x", Call("Matrix", a, a, r))],
            Eqn(Apply(Apply(Qualified("MatrixMap", "conj"), y), x),
                Mul(Mul(y, x), Call("conjTranspose", y))));
        return Disp(All([Bound("A", Named("Type")), Bound("B", Named("Type")),
            Bound("R", Named("Type"))],
            Seq(Instance("Fintype", a), Instance("RCLike", r), statement)));
    }

    private static Formula AddKronFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), c = F.Id("C"), d = F.Id("D"), r = F.Id("R");
        Formula ml1 = F.Id("ML1"), ml2 = F.Id("ML2"), mr = F.Id("MR");
        Formula Kron(Formula left) => Apply(Qualified("MatrixMap", "kron"), left, mr);
        Formula statement = All([Bound("ML1", MatrixMapOf(a, b, r)),
            Bound("ML2", MatrixMapOf(a, b, r)), Bound("MR", MatrixMapOf(c, d, r))],
            Eqn(Kron(Add(ml1, ml2)), Add(Kron(ml1), Kron(ml2))));
        return Disp(All([Bound("A", Named("Type")), Bound("B", Named("Type")),
            Bound("C", Named("Type")), Bound("D", Named("Type")), Bound("R", Named("Type"))],
            Seq(Instance("Fintype", a), Instance("DecidableEq", a), Instance("Fintype", b),
                Instance("Fintype", c), Instance("Fintype", d), Instance("DecidableEq", c),
                Instance("CommSemiring", r), statement)));
    }

    private static Formula AddCpFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), r = F.Id("R"), m1 = F.Id("M1"), m2 = F.Id("M2");
        Formula Cp(Formula map) => Apply(Qualified("MatrixMap", "IsCompletelyPositive"), map);
        Formula implication = new Formula.Logic(Cp(m1), FormulaLogicOperator.Implies,
            new Formula.Logic(Cp(m2), FormulaLogicOperator.Implies, Cp(Add(m1, m2))));
        return Disp(All([Bound("A", Named("Type")), Bound("B", Named("Type")), Bound("R", Named("Type"))],
            Seq(Instance("Fintype", a), Instance("DecidableEq", a), Instance("Fintype", b),
                Instance("RCLike", r), All([Bound("M1", MatrixMapOf(a, b, r)),
                    Bound("M2", MatrixMapOf(a, b, r))], implication))));
    }

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), rtype = F.Id("R");
        Formula r = F.Id("r"), k = F.Id("K"), channel = F.Id("C"), rho = F.Id("rho");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula ka = new Formula.Apply(k, [r]);
        Formula input = Call("Matrix", a, a, complex);
        Formula SumOver(Formula body) => Seq(Sum, Underscore,
            Grp(r, Sp, InMacro, Sp, rtype), Sp, body);
        Formula completeness = Eqn(SumOver(Mul(Conj(ka), ka)), Num(1));
        Formula action = All([Bound("rho", input)], Eqn(
            Call("fromCstar", Call("apply", channel, Call("toCstar", rho))),
            SumOver(Mul(Mul(ka, rho), Conj(ka)))));
        Formula result = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("C", Call("QuantumChannel", a, b))], action);
        return Disp(All(
            [Bound("A", F.Id("FiniteType")), Bound("B", F.Id("FiniteType")),
                Bound("R", F.Id("FiniteType")),
                Bound("K", new Formula.TypeArrow(rtype, Call("Matrix", b, a, complex)))],
            new Formula.Logic(completeness, FormulaLogicOperator.Implies, result)));
    }
}
