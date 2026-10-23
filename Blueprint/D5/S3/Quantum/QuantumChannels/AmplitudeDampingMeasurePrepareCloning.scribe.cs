using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class AmplitudeDampingMeasurePrepareCloningDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/AmplitudeDampingMeasurePrepareCloning";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/sekatskiguryanovakothakondaskotiniotis2025cloning");

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) =>
        App(Named(name), arguments);
    private static Formula Qualified(string owner, string name, params Formula[] arguments) =>
        App(Seq(Named(owner), Dot, Named(name)), arguments);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula Product(Formula left, Formula right) =>
        Parenthesized(Seq(left, Sp, Times, Sp, right));
    private static Formula Site => Product(Fin(D(2)), Fin(D(2)));
    private static Formula Sites(Formula n) => Arrow(Fin(n), Site);
    private static Formula Bits(Formula n) => Arrow(Fin(n), Fin(D(2)));
    private static Formula Matrix(Formula index) => Call("Matrix", index, index, Complexes);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula LambdaOf(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(variable, type), Sp, Mapsto, Sp, body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffOf(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula SumOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(variable, type)), Sp, Parenthesized(body));
    private static Formula ProductOver(Formula variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Typed(variable, type)), Sp, Parenthesized(body));
    private static Formula Pair(Formula left, Formula right) =>
        Parenthesized(Seq(left, Comma, Sp, right));
    private static Formula Component(Formula value, byte index) => Seq(value, Dot, D(index));
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Call("ite", Parenthesized(condition), yes, no);
    private static Formula Smul(Formula scalar, Formula matrix) =>
        Call("smul", scalar, matrix);
    private static Formula SqrtReal(Formula value) => Qualified("Real", "sqrt", value);
    private static Formula OfReal(Formula value) => Qualified("Complex", "ofReal", value);
    private static Formula MatrixTwo(Formula a, Formula b, Formula c, Formula d) => Seq(
        Begin, Grp(F.Id("pmatrix")), a, Amp, b, RowBreak, c, Amp, d,
        End, Grp(F.Id("pmatrix")));

    private static Formula AdChoiDefinition()
    {
        Formula gamma = GammaLower, a = F.Id("A"), x = F.Id("x"), y = F.Id("y"), k = F.Id("k");
        var zero = Typed(D(0), Complexes);
        var one = Typed(D(1), Complexes);
        var kraus = Seq(Bang, OpenBracket,
            MatrixTwo(one, zero, zero, OfReal(SqrtReal(Subtract(Typed(D(1), Reals), gamma)))),
            Comma, Sp, MatrixTwo(zero, OfReal(SqrtReal(gamma)), zero, zero), CloseBracket);
        var entry = SumOver(k, Fin(D(2)), Multiply(
            App(a, k, Component(x, 2), Component(x, 1)),
            Call("star", App(a, k, Component(y, 2), Component(y, 1)))));
        var body = Parenthesized(Seq(Named("let"), Sp,
            Typed(a, Arrow(Fin(D(2)), Matrix(Fin(D(2))))), Sp, Colon, Eq, Sp, kraus,
            Semi, Sp, LambdaOf(x, Site, LambdaOf(y, Site, entry))));
        return All(gamma, Reals, Equal(Call("adChoi", gamma), body));
    }

    private static Formula ChoiPowDefinition()
    {
        Formula j = F.Id("J"), n = F.Id("n"), x = F.Id("x"), y = F.Id("y"), i = F.Id("i");
        return All(j, Matrix(Site), All(n, Naturals, Equal(Call("choiPow", j, n),
            LambdaOf(x, Sites(n), LambdaOf(y, Sites(n),
                ProductOver(i, Fin(n), App(j, App(x, i), App(y, i))))))));
    }

    private static Formula ChannelDefinition()
    {
        Formula n = F.Id("n"), k = F.Id("K"), r = F.Id("r"),
            rPrime = Seq(F.Id("r"), Apos), o = F.Id("o"), i = F.Id("i");
        var marginal = All(r, Bits(n), All(rPrime, Bits(n), Equal(
            SumOver(o, Bits(n), App(k,
                LambdaOf(i, Fin(n), Pair(App(r, i), App(o, i))),
                LambdaOf(i, Fin(n), Pair(App(rPrime, i), App(o, i))))),
            If(Equal(r, rPrime), Typed(D(1), Complexes), Typed(D(0), Complexes)))));
        return All(n, Naturals, All(k, Matrix(Sites(n)), IffOf(Call("IsChannelChoi", k),
            And(Qualified("Matrix", "PosSemidef", k), marginal))));
    }

    private static Formula Weight(Formula t, Formula ell, Formula gamma, Formula n) =>
        Qualified("Matrix", "trace", Multiply(App(t, ell),
            Call("choiPow", Call("adChoi", gamma), n)));

    private static Formula ClaimBody()
    {
        Formula n = F.Id("N"), m = F.Id("M"), l = F.Id("L"), t = F.Id("T"), k = F.Id("K"),
            ell = Ell, gamma = GammaLower;
        var weight = Weight(t, ell, gamma, n);
        var atGamma = And(All(ell, Fin(l), AtMost(Typed(D(0), Complexes), weight)),
            And(Equal(SumOver(ell, Fin(l), weight), Typed(D(1), Complexes)),
                Equal(SumOver(ell, Fin(l), Smul(weight, App(k, ell))),
                    Call("choiPow", Call("adChoi", gamma), m))));
        var parameters = All(gamma, Reals, Implies(
            new Formula.Relation(gamma, FormulaRelationOperator.MemberOf,
                Qualified("Set", "Icc", Typed(D(0), Reals), Typed(D(1), Reals))), atGamma));
        var ensemble = Some(l, Naturals,
            Some(t, Arrow(Fin(l), Matrix(Sites(n))),
                Some(k, Arrow(Fin(l), Matrix(Sites(m))),
                    And(All(ell, Fin(l), Call("IsChannelChoi", App(k, ell))), parameters))));
        return All(n, Naturals, All(m, Naturals,
            Implies(AtMost(Typed(D(1), Naturals), m), new Formula.Not(Parenthesized(ensemble)))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No finite measure-and-prepare ensemble perfectly clones every amplitude-damping channel into a positive number of outputs.",
        H("Amplitude-damping channels resist perfect measure-and-prepare cloning"),
        Blocks(
            Paragraph(Text(
                "Matrix indices place the reference qubit before the output qubit. All Choi matrices "
                + "are unnormalized: tracing out the output gives the identity on the reference. "
                + "The functions Complex.ofReal in the formulas explicitly embed real numbers into the complex field; "
                + "star is complex conjugation, and smul is scalar multiplication of a matrix. "
                + "The order on complex scalars means that a nonnegative scalar is real and nonnegative.")),
            Describe.Lean(
                DescribeId.Create("ad-choi"),
                DeclarationHandle.Create(Module + ".adChoi"),
                H("The amplitude-damping Choi matrix"),
                StatementSource.FromAuthor(Disp(AdChoiDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The two Kraus matrices are those of the amplitude-damping family in arxiv_v1.tex, "
                    + "lines 1538–1553. For a real damping parameter gamma, their matrix entries define "
                    + "the Choi matrix by summing each Kraus entry against the conjugate of the other. "
                    + "The definition accepts every real gamma; the channel interpretation uses gamma in [0,1]. "
                    + "On this interval the reference marginal is the identity and the trace is two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("choi-pow"),
                DeclarationHandle.Create(Module + ".choiPow"),
                H("Tensor powers in coordinates"),
                StatementSource.FromAuthor(Disp(ChoiPowDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The n-fold tensor power has rows and columns indexed by assignments of one "
                    + "reference-output pair to each site in Fin n. An entry is the product of the "
                    + "corresponding single-site entries. The empty tensor power has one row, one column, "
                    + "and its sole entry is one."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-channel-choi"),
                DeclarationHandle.Create(Module + ".IsChannelChoi"),
                H("Positivity and the reference marginal"),
                StatementSource.FromAuthor(Disp(ChannelDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A channel Choi matrix is positive semidefinite and has reference marginal equal "
                    + "to the identity. The sum uses the same output assignment o in both matrix indices. "
                    + "This condition allows an arbitrary global channel on n qubits, including channels "
                    + "whose Choi matrices do not factor over the sites."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("The finite measure-and-prepare impossibility statement"),
                StatementSource.FromAuthor(Disp(Equal(Named("claim"), Parenthesized(ClaimBody())))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "The source defines measure-and-prepare cloning as a measurement followed by "
                        + "an outcome-dependent global channel preparation, in arxiv_v1.tex, lines 1094–1099. "
                        + "Its conjecture at lines 1684–1685 excludes perfect cloning at N = M. "
                        + "The displayed formulation ranges over every natural N, including zero, "
                        + "and every positive M, with a finite number L of outcomes.")),
                    Paragraph(Text(
                        "Each fixed matrix T indexed by an outcome gives that outcome's probability "
                        + "as its trace pairing with the N-fold input Choi matrix. These complex trace "
                        + "values must be nonnegative and sum to one for every gamma in [0,1]. "
                        + "The fixed preparation matrices K are global channel Choi matrices. Their "
                        + "probability-weighted sum would have to equal the M-fold target Choi matrix "
                        + "throughout the interval. The trace representation of a finite measurement "
                        + "process supplies the physical interpretation of T; the statement quantifies "
                        + "over all matrices satisfying the displayed scalar conditions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Polynomial probabilities contradict exact cloning"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Put gamma = 1 − s² with s in [0,1]. In the ordered basis (00,01,10,11), "
                        + "the Choi matrix is w times its conjugate transpose plus Complex.ofReal(1 − s²) "
                        + "times u times its conjugate transpose, where w = (1,0,0,Complex.ofReal(s)) "
                        + "and u = (0,0,1,0). "
                        + "Consequently every entry is a polynomial in s. Summing over the output "
                        + "index gives the identity reference marginal. The (00,11) entry is "
                        + "Complex.ofReal(s), so two such Choi matrices are equal only when their "
                        + "parameters s are equal.")),
                    Paragraph(Text(
                        "For a preparation on n + 1 qubits, fix every reference site except the first "
                        + "to zero and trace out the other n output sites. The resulting matrix is a "
                        + "qubit channel Choi matrix: positivity follows by restricting a positive "
                        + "semidefinite matrix to a submatrix and taking a partial trace, while its "
                        + "reference marginal follows by summing the original channel marginal over "
                        + "the remaining output assignments. Applied to a tensor power of a matrix J, "
                        + "this operation gives J multiplied by the n-th power of the sum of "
                        + "J((0,o),(0,o)) over o in Fin 2. For the amplitude-damping matrix that sum "
                        + "is one, so the operation gives its single-qubit Choi matrix. Finite sums "
                        + "and scalar multiplication commute with this operation.")),
                    Paragraph(Text(
                        "Next suppose that the single-qubit Choi matrix at s is a sum of nonnegative "
                        + "weights q times channel Choi matrices R. Choose an outcome ell with nonzero "
                        + "weight. Every vector annihilated by the sum is annihilated by R at ell: "
                        + "the corresponding quadratic forms are nonnegative, their weighted sum is "
                        + "zero, and positive semidefiniteness turns a zero quadratic form into a "
                        + "zero matrix-vector product. Apply this first to the basis vector at 01, "
                        + "then to Complex.ofReal(s) times the basis vector at 00 minus the basis vector at 11. "
                        + "The 01 column vanishes, and the 11 column is Complex.ofReal(s) times the 00 column. "
                        + "Hermitian symmetry gives the corresponding row relations.")),
                    Paragraph(Text(
                        "The channel marginal now fixes the remaining entries of R at ell. "
                        + "The (00,00) entry is one and the (00,10) entry is zero; Hermitian symmetry "
                        + "makes the (10,00) entry zero. The (11,00) entry is Complex.ofReal(s), "
                        + "the (11,10) entry is zero, and the (10,10) entry is one minus "
                        + "Complex.ofReal(s) squared. Together with the column and row relations "
                        + "these determine every entry and give precisely the amplitude-damping "
                        + "Choi matrix at s. Thus any summand with nonzero weight must be that matrix. "
                        + "This argument includes both endpoints of the interval.")),
                    Paragraph(Text(
                        "For a fixed input matrix T, form a complex polynomial by summing over "
                        + "row and column assignments x and y: each summand is the constant "
                        + "coefficient T(x,y) times the product, over all input sites i, of the "
                        + "polynomial entry at (y(i),x(i)). Evaluation at Complex.ofReal(s) is "
                        + "exactly the trace pairing of T with the N-fold Choi matrix at gamma = 1 − s². "
                        + "If a fixed matrix R must equal the amplitude-damping matrix whenever "
                        + "this polynomial is nonzero, then the polynomial is identically zero. "
                        + "Indeed, either it vanishes everywhere on [0,1], or a point t where it is "
                        + "nonzero forces every other nonzero point to equal t, by the (00,11) entry. "
                        + "In either case it has infinitely many distinct complex roots, since "
                        + "the real interval remains infinite after removing one point and the "
                        + "embedding into the complex field is injective.")),
                    Paragraph(Text(
                        "Finally assume a finite ensemble satisfying the claim's equalities and "
                        + "write M = n + 1. For each outcome ell, take its trace polynomial and "
                        + "the fixed qubit channel obtained from K at ell by the preceding reduction. "
                        + "At every s in [0,1], the ensemble equality reduces to a nonnegative sum "
                        + "equal to the single-qubit amplitude-damping matrix. A nonzero polynomial "
                        + "value is a nonzero weight, so the summand argument forces that fixed "
                        + "qubit channel to equal the amplitude-damping matrix at s. The polynomial "
                        + "therefore vanishes identically. Evaluating it at s = 0 makes every "
                        + "outcome probability at gamma = 1 zero, contradicting their sum being one. "
                        + "The contradiction holds for every N and every positive M."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("sekatski-guryanova-kothakonda-skotiniotis-2025-amplitude-damping-measure-prepare-cloning"),
                    ResolutionKind.Proved)))));
}
