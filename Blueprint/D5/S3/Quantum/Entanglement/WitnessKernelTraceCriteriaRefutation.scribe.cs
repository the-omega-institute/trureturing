using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class WitnessKernelTraceCriteriaRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/WitnessKernelTraceCriteriaRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/vomende2025witnessoptimality");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The kernel criterion for optimality of entanglement witnesses does not imply the trace criterion.",
        H("The kernel and trace criteria are not equivalent"),
        Blocks(
            Paragraph(Text("The dimensions m and n are arbitrary natural numbers. Fin m and Fin n index the two factors, and all matrices and vectors have complex entries. A product vector has coordinate x(p.1)y(p.2). star denotes complex conjugation, dotProduct is the bilinear coordinate sum, mulVec is matrix action, and kronecker is the Kronecker product of matrices. Complex nonnegativity requires a nonnegative real part and zero imaginary part. toLp places a coordinate vector in EuclideanSpace with its standard inner product. The Lean names trTwo and trOne have notation tr₂ and tr₁, respectively. ofReal and natCastComplex display the scalar embeddings used in Lean.")),
            Definition("blockPositive", "Block positivity", BlockPositiveFormula(),
                "Section II B requires a nonnegative complex expectation on every product vector, without normalization assumptions on either factor."),
            Definition("IsWitness", "Entanglement witnesses", WitnessFormula(),
                "A block-positive matrix is a witness when some positive semidefinite matrix sigma satisfies the strict negative trace inequality tr(W sigma) < 0."),
            Definition("trTwo", "Trace over the second factor", PartialTraceFormula(false),
                "trTwo is the existing partialTraceRight: sum over the repeated second index while retaining the first factor."),
            Definition("trOne", "Trace over the first factor", PartialTraceFormula(true),
                "trOne is the existing partialTraceLeft: sum over the repeated first index while retaining the second factor."),
            Definition("schmidtRank", "Schmidt rank", SchmidtFormula(),
                "Remark 3(i) defines Schmidt rank as the rank of the vector's coefficient matrix."),
            Definition("kernelCriterion", "The kernel criterion", KernelFormula(),
                "Theorem 2 uses a full Schmidt-rank vector in one of the two partial-trace-shifted kernels. Both alternatives, with their dimension inequalities, are retained."),
            Definition("maximallyEntangled", "Maximally entangled states", MaximalFormula(),
                "Corollary 2 uses min(m,n) orthonormal vectors in each factor with every Schmidt coefficient equal to min(m,n) raised to negative one half. The orthonormality predicates use the standard complex Euclidean inner product."),
            Definition("traceCriterion", "The trace criterion", TraceFormula(),
                "The trace criterion is equality in equation (11) for at least one maximally entangled state. The equality is an equality of complex numbers."),
            Definition("claim", "The equivalence question", IffTo(V("claim"), ClaimBody()),
                "Section IV asks whether the trace-based criterion of Corollary 2 is equivalent to the kernel criterion of Theorem 2. The statement quantifies over all finite dimensions and every witness."),
            Describe.Lean(DescribeId.Create("vomende-kernel-trace-result"),
                DeclarationHandle.Create(Prefix + "result"), H("The equivalence is false"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, V("claim")))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "In the ordered basis (00,01,10,11), take W with rows (0,0,0,-2), (0,1,0,0), (0,0,4,0), (-2,0,0,0). Its product expectation is the squared modulus of conjugate(x(0))y(1)-2conjugate(x(1))y(0), so it is block positive. The Bell vector (1,0,0,1)/sqrt(2) gives a positive semidefinite outer product with trace pairing -2. The second partial trace is diag(1,4); the shifted matrix annihilates (2,0,0,1), whose coefficient matrix diag(2,1) has rank two. Every maximally entangled state has squared norm one. For any z, the quadratic form of W+2I is 2|z(00)-z(11)| squared plus 3|z(01)| squared plus 6|z(10)| squared. Consequently every such state's expectation is at least -2, whereas the trace criterion requires -5/2. Thus this witness satisfies the kernel criterion and fails the trace criterion. This conclusion does not alter either criterion's sufficient implication to optimality."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("vom-ende-cichy-2025-kernel-trace-criteria-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("vomende-kernel-trace-" +
            name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) =>
        new Formula.Relation(a, op, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula IffTo(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Pair(Formula a, Formula b) => Call("Prod", a, b);
    private static Formula Index() => Pair(Fin(V("m")), Fin(V("n")));
    private static Formula Vec(Formula index) => Arrow(index, V("Complex"));
    private static Formula Mat() => Call("Matrix", Index(), Index(), V("Complex"));
    private static Formula Dim(Formula body) => All("m", V("Nat"), All("n", V("Nat"), body));
    private static Formula WithMatrix(Formula body) => Dim(All("W", Mat(), body));
    private static Formula MinDim() => Call("min", V("m"), V("n"));
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, type, Comma, Sp, body);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Grp(Seq(V(name), Colon, type))), Parenthesized(body));
    private static Formula Tensor(Formula x, Formula y) => Lam("p", Index(),
        Multiply(At(x, Call("fst", V("p"))), At(y, Call("snd", V("p")))));
    private static Formula Expect(Formula w, Formula z) =>
        Call("dotProduct", Call("star", z), Call("mulVec", w, z));

    private static Formula BlockPositiveFormula()
    {
        var product = Parenthesized(Tensor(V("x"), V("y")));
        return WithMatrix(IffTo(Call("blockPositive", V("W")),
            All("x", Vec(Fin(V("m"))), All("y", Vec(Fin(V("n"))),
                Le(D(0), Expect(V("W"), product))))));
    }
    private static Formula WitnessFormula() => WithMatrix(IffTo(Call("IsWitness", V("W")),
        And(Call("blockPositive", V("W")), Ex("sigma", Mat(),
            And(Call("PosSemidef", V("sigma")), Lt(Call("trace",
                Multiply(V("W"), V("sigma"))), D(0)))))));
    private static Formula PartialTraceFormula(bool left)
    {
        var first = left ? "j" : "i"; var second = left ? "l" : "k";
        var sum = left ? "i" : "j";
        var dimension = V(left ? "n" : "m"); var tracedDimension = V(left ? "m" : "n");
        Formula Entry(string retained) => left
            ? Call("pair", V(sum), V(retained)) : Call("pair", V(retained), V(sum));
        return WithMatrix(All(first, Fin(dimension), All(second, Fin(dimension),
            Equal(At(Call(left ? "trOne" : "trTwo", V("W")), V(first), V(second)),
                SumOver(sum, Fin(tracedDimension), At(V("W"), Entry(first), Entry(second)))))));
    }
    private static Formula SchmidtFormula() => Dim(All("v", Vec(Index()),
        Equal(Call("schmidtRank", V("v")), Call("rank", Call("of",
            Parenthesized(Lam("i", Fin(V("m")), Lam("j", Fin(V("n")),
                At(V("v"), Call("pair", V("i"), V("j")))))))))));
    private static Formula KernelFormula()
    {
        Formula Side(bool second)
        {
            var shift = second
                ? Call("kronecker", Call("trTwo", V("W")), D(1))
                : Call("kronecker", D(1), Call("trOne", V("W")));
            var size = V(second ? "m" : "n"); var other = V(second ? "n" : "m");
            return And(Le(size, other), Ex("v", Vec(Index()),
                And(Equal(Call("mulVec", Parenthesized(Add(V("W"), shift)), V("v")), D(0)),
                    Equal(Call("schmidtRank", V("v")), size))));
        }
        return WithMatrix(IffTo(Call("kernelCriterion", V("W")), Or(Side(true), Side(false))));
    }
    private static Formula MaximalFormula()
    {
        var familyU = Arrow(Fin(MinDim()), Vec(Fin(V("m"))));
        var familyW = Arrow(Fin(MinDim()), Vec(Fin(V("n"))));
        Formula Orth(string name) => Call("Orthonormal", V("Complex"), Parenthesized(
            Lam("j", Fin(MinDim()), Call("toLp", D(2), At(V(name), V("j"))))));
        var coefficient = Call("ofReal", new Formula.Power(Call("natCastReal", MinDim()),
            new Formula.Negate(new Formula.Fraction(D(1), D(2)))));
        var sum = SumOver("j", Fin(MinDim()), Call("smul", coefficient,
            Parenthesized(Tensor(At(V("u"), V("j")), At(V("w"), V("j"))))));
        return Dim(All("Omega", Vec(Index()), IffTo(Call("maximallyEntangled", V("Omega")),
            Ex("u", familyU, Ex("w", familyW,
                And(Orth("u"), And(Orth("w"), Equal(V("Omega"), sum))))))));
    }
    private static Formula TraceFormula() => WithMatrix(IffTo(Call("traceCriterion", V("W")),
        Ex("Omega", Vec(Index()), And(Call("maximallyEntangled", V("Omega")),
            Equal(Expect(V("W"), V("Omega")), new Formula.Negate(new Formula.Fraction(
                Call("trace", V("W")), Call("natCastComplex", MinDim()))))))));
    private static Formula ClaimBody() => WithMatrix(Imp(Call("IsWitness", V("W")),
        IffTo(Call("kernelCriterion", V("W")), Call("traceCriterion", V("W")))));
}
