using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class ClauseHamiltonianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full complex matrix exponential encodes the raw Boolean satisfying count.",
        H("Raw Clause Hamiltonian and Full Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("clause-partition-recovery"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Dynamics/ClauseHamiltonian.clause_partition_recovery"),
                H("Dyadic partition and integer count recovery"),
                StatementSource.FromAuthor(Presentation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Each raw clause determines the diagonal projector onto its "
                        + "violating assignments. The hidden Hamiltonian is n plus one "
                        + "times their sum. The full Hamiltonian is the visible one-state "
                        + "projector tensor the hidden identity, plus the visible identity "
                        + "tensor that hidden Hamiltonian. The inverse temperature is log two.")),
                    Paragraph(Text(
                        "The partition is defined as the trace of the genuine complex "
                        + "matrix exponential, independently of the count. If m is the "
                        + "raw clause count and N sums two to the power (n plus one) "
                        + "times m minus the number of violated clauses over every "
                        + "assignment, the full partition is three N divided by two "
                        + "to the power (n plus one) m plus one.")),
                    Paragraph(Text(
                        "The floor of two thirds of the real partition is exactly the "
                        + "number of satisfying assignments in the declared universe. "
                        + "The unsatisfying Boltzmann tail is between zero and one half. "
                        + "All universe sizes, including the zero-variable singleton, "
                        + "and all raw clause lists are covered.")),
                    Paragraph(Text(
                        "Every clause is a Hermitian idempotent diagonal projector. Its "
                        + "diagonal depends only on its literal variables, whose number "
                        + "is at most the clause length. The exact normalized partial "
                        + "traces give the visible centered projector and the hidden "
                        + "Hamiltonian shifted by one half of the identity. Their tensor "
                        + "sum is the original full Hamiltonian, and every visible "
                        + "commutator remains in the complete visible matrix algebra. "
                        + "All clause projectors commute; an empty clause is the identity "
                        + "projector. The normalized conditional-expectation residual "
                        + "vanishes for every visible matrix. For every joint matrix "
                        + "and every real time, its evolved visible marginal is exactly "
                        + "the marginal evolved by the same centered visible Hamiltonian.")),
                    Paragraph(Text(
                        "The display uses the actual named Hamiltonian, projector, partition "
                        + "and count definitions. identity carries its displayed finite "
                        + "carrier; tensor is the Kronecker product, scale is scalar "
                        + "multiplication, and adjoint is conjugate transpose. exp is the "
                        + "actual matrix exponential and re is the complex real part. "
                        + "castNat and castInt are the displayed natural and integer casts. "
                        + "ofMatrix is the CStar matrix image; underlyingMatrix extracts "
                        + "the ordinary matrix from a density state. eval and apply "
                        + "denote function and matrix entries.")),
                    Paragraph(Text(
                        "The five self-adjointness witnesses concern minus log two times "
                        + "the full, visible, hidden, centered visible and shifted hidden "
                        + "Hamiltonians, respectively. gibbsState is the positive "
                        + "trace-one normalized exponential of that exponent. The full "
                        + "Gibbs state is the product of the centered visible Gibbs "
                        + "state and the hidden Gibbs state. Both scalar shifts leave "
                        + "their Gibbs states unchanged; the actual hidden marginal is "
                        + "the hidden Gibbs state. At zero variables it is the singleton identity.")),
                    Paragraph(Text(
                        "Every visible density state, including singular ones, is "
                        + "supported inside the centered visible Gibbs state, and its product "
                        + "with the hidden Gibbs state is supported inside the full Gibbs "
                        + "state. extendedQuantumRelativeEntropy is the support-aware "
                        + "entropy; quantumRelativeEntropy is its finite trace-log branch. The actual visible "
                        + "marginal, equality of extended relative entropies, zero finite "
                        + "defect and zero reconstruction relative entropy all hold for "
                        + "this identical Hamiltonian."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "This identity does not itself establish a canonical rational word, "
                + "a query codec, an operational one-query protocol or efficient "
                + "hidden Gibbs preparation."))),
        []));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula And(params Formula[] clauses) =>
        clauses.Reverse().Aggregate((right, left) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Scale(Formula scalar, Formula matrix) => Call("scale", scalar, matrix);
    private static Formula Tensor(Formula left, Formula right) => Call("tensor", left, right);
    private static Formula Matrix(Formula carrier) => Call("Matrix", carrier, carrier, Id("Complex"));
    private static Formula Identity(Formula carrier) => Call("identity", carrier);
    private static Formula NatCast(Formula value) => Call("castNat", value);

    private static Formula Presentation()
    {
        var n = Id("n");
        var f = Id("F");
        var assignments = Call("Assignment", n);
        var joint = Call("Prod", Id("Bool"), assignments);
        var clauseType = Call("Clause", Call("Fin", n));
        var hf = Call("hiddenHamiltonian", f);
        var h = Call("fullHamiltonian", f);
        var p = Id("visibleProjector");
        var ia = Identity(Id("Bool"));
        var ib = Identity(assignments);
        var half = new Formula.Fraction(Num(1), Num(2));
        var ac = Subtract(p, Scale(half, ia));
        var bc = Add(hf, Scale(half, ib));
        var dimension = NatCast(Call("card", assignments));
        var right = Call("partialTraceRight", h);
        var centered = Subtract(Scale(new Formula.Power(dimension, new Formula.Negate(Num(1))), right),
            Scale(new Formula.Fraction(Call("trace", h), Multiply(Num(2), dimension)), ia));
        var partition = Call("fullPartition", f);
        var numerator = Call("partitionNumerator", f);
        var k = Multiply(Add(n, Num(1)), Call("length", f));
        var count = And(
            Equal(partition, new Formula.Fraction(Multiply(Num(3), NatCast(numerator)),
                new Formula.Power(Num(2), Add(k, Num(1))))),
            Equal(new Formula.Floor(Multiply(new Formula.Fraction(Num(2), Num(3)),
                Call("re", partition))), Call("castInt", Call("satisfyingCount", f))));
        var c = Id("c");
        var d = Id("d");
        var proj = Call("clauseProjector", c);
        var support = Id("s");
        var a = Id("a");
        var b = Id("b");
        var i = Id("i");
        var agrees = All("i", Call("Fin", n), Implies(Call("mem", i, support),
            Equal(Call("eval", a, i), Call("eval", b, i))));
        var locality = Exists("s", Call("Finset", Call("Fin", n)), And(
            Le(Call("card", support), Call("length", c)),
            All("a", assignments, All("b", assignments, Implies(agrees,
                Equal(Call("apply", proj, a, a), Call("apply", proj, b, b)))))));
        var projectors = All("c", clauseType, Implies(Call("mem", c, f), And(
            Call("IsHermitian", proj), Equal(Multiply(proj, proj), proj), locality)));
        var m = Id("M");
        var commutator = Subtract(Multiply(h, Tensor(m, ib)), Multiply(Tensor(m, ib), h));
        var visibleCommutator = Tensor(Subtract(Multiply(p, m), Multiply(m, p)), ib);
        var leakage = All("M", Matrix(Id("Bool")), Equal(Subtract(commutator,
            Tensor(Scale(new Formula.Power(dimension, new Formula.Negate(Num(1))),
                Call("partialTraceRight", commutator)), ib)), Num(0)));
        var t = Id("t");
        var rho = Id("rho");
        var minusIt = Multiply(new Formula.Negate(Num(1)), Multiply(Id("complexI"), Call("castReal", t)));
        var u = Call("exp", Scale(minusIt, h));
        var ua = Call("exp", Scale(minusIt, ac));
        var evolution = All("t", Id("Real"), All("rho", Matrix(joint),
            Equal(Call("partialTraceRight", Multiply(Multiply(u, rho), Call("adjoint", u))),
                Multiply(Multiply(ua, Call("partialTraceRight", rho)), Call("adjoint", ua)))));
        var minusBeta = Multiply(new Formula.Negate(Num(1)), Call("castReal", Call("log", Num(2))));
        var x = Call("ofMatrix", Scale(minusBeta, h));
        var xa = Call("ofMatrix", Scale(minusBeta, p));
        var xb = Call("ofMatrix", Scale(minusBeta, hf));
        var xac = Call("ofMatrix", Scale(minusBeta, ac));
        var xbc = Call("ofMatrix", Scale(minusBeta, bc));
        var gx = Call("gibbsState", x, Id("hX"));
        var ga = Call("gibbsState", xa, Id("hA"));
        var gb = Call("gibbsState", xb, Id("hB"));
        var gac = Call("gibbsState", xac, Id("hAc"));
        var gbc = Call("gibbsState", xbc, Id("hBc"));
        var product = Call("productState", rho, gb);
        var entropy = All("rho", Call("DensityState", Id("Bool")), And(
            Call("SupportContained", rho, gac),
            Call("SupportContained", product, gx),
            Equal(Call("partialTraceRight", Call("underlyingMatrix", product)),
                Call("underlyingMatrix", rho)),
            Equal(Call("extendedQuantumRelativeEntropy", product, gx),
                Call("extendedQuantumRelativeEntropy", rho, gac)),
            Equal(Subtract(Call("quantumRelativeEntropy", product, gx),
                Call("quantumRelativeEntropy", rho, gac)), Num(0)),
            Equal(Call("extendedQuantumRelativeEntropy", product, product), Num(0))));
        var gibbs = Exists("hX", Call("IsSelfAdjoint", x),
            Exists("hA", Call("IsSelfAdjoint", xa),
            Exists("hB", Call("IsSelfAdjoint", xb),
            Exists("hAc", Call("IsSelfAdjoint", xac),
            Exists("hBc", Call("IsSelfAdjoint", xbc), And(
                Equal(gx, Call("productState", gac, gb)),
                Equal(gac, ga), Equal(gbc, gb),
                Equal(Call("partialTraceLeft", Call("underlyingMatrix", gx)),
                    Call("underlyingMatrix", gb)),
                Implies(Equal(n, Num(0)), Equal(Call("underlyingMatrix", gb), ib)), entropy))))));
        return All("n", Id("Nat"), All("F", Call("Formula", n), And(
            count, Call("IsHermitian", hf), Call("IsHermitian", h), projectors,
            Equal(centered, ac), Equal(Scale(half, Call("partialTraceLeft", h)), bc),
            Equal(h, Add(Tensor(ac, ib), Tensor(ia, bc))),
            All("M", Matrix(Id("Bool")), Equal(commutator, visibleCommutator)),
            All("c", clauseType, All("d", clauseType,
                Equal(Multiply(proj, Call("clauseProjector", d)),
                    Multiply(Call("clauseProjector", d), proj)))),
            Equal(Call("clauseProjector", Call("nil", clauseType)), ib),
            leakage, evolution, gibbs)));
    }

}
