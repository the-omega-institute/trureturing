using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class PauliRotationCriticalValuesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/PauliRotationCriticalValues.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumChannels/wierichs2025brickwall");
    private static readonly LibraryNoteRef AnalyticZeros =
        LibraryNoteRef.Create("D5/L/AnalyticClosure/mityagin2015zeroset");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A product of fifteen two-qubit Pauli rotations has full derivative rank almost everywhere, while its critical values have Hausdorff dimension at least fourteen.",
        H("Pauli rotations with a hypersurface of critical values"),
        Blocks(
            Node("BasisState", "Two-qubit basis labels",
                Disp(Equal(Named("BasisState"), Arrow(Fin(D(2)), Fin(D(2))))),
                "A basis label assigns a bit to each of the two qubits. There are four labels.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("Mat", "Complex matrices on two qubits",
                Disp(Equal(Named("Mat"), Call("Matrix", Named("BasisState"), Named("BasisState"), Complexes()))),
                "Rows and columns are indexed by BasisState, so Mat is the space of four-by-four complex matrices. The matrix norm is the Frobenius norm.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("Param", "Fifteen real rotation angles",
                Disp(Equal(Named("Param"), Arrow(Fin(D(1,5)), Reals()))),
                "The fifteen coordinates are independent real angles, indexed from zero through fourteen.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("NonIdentityPauli", "Nonidentity two-qubit Pauli words", PauliFormula(),
                "Pauli has the four letters Pauli.I, Pauli.X, Pauli.Y and Pauli.Z. Excluding the constant identity word leaves fifteen words. Function.const(Fin 2, Pauli.I) is the function assigning Pauli.I to both qubits.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("rotation", "A Pauli rotation", RotationFormula(),
                "wordOp takes the tensor product of the two Pauli matrices. SMul.smul is scalar multiplication: Real.cos and Real.sin act as real scalars on Mat, while Complex.I acts as a complex scalar. The typed 1 is the identity matrix. This is the rotation with generator wordOp(p.val) and angle a.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("circuit", "The ordered product of fifteen rotations", CircuitFormula(),
                "List.ofFn lists the rotations in increasing Fin 15 order, and List.prod multiplies them from left to right. Each coordinate feeds into exactly one rotation. The sequence P may repeat words.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("derivativeRank", "Real rank of the circuit derivative", RankFormula(),
                "fderiv is the Frechet derivative over the real numbers. Its toLinearMap projection has a real vector-space range, whose Module.finrank is the rank. The domain has real dimension fifteen.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("critical", "Parameters of deficient derivative rank", CriticalFormula(),
                "The critical set consists of the parameters where the real derivative rank is strictly less than fifteen. Its image under circuit is the set of critical values.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("claim", "Conjecture 3 in the two-qubit case", ClaimFormula(),
                "Wierichs, Kottmann and Killoran, Conjecture 3, §V, p. 9: \"The critical values F(C) of a PQC that has full rank almost everywhere in T^d form an at most (d−2)-dimensional subset of G.\" Here d = 15 and G is SU(4), represented by its complex matrices. The displayed proposition quantifies over every sequence of fifteen nonidentity two-qubit Pauli words. Its premise uses Lebesgue volume on Param, and its conclusion uses the Hausdorff dimension dimH of the actual matrix image. The measure beneath the almost-everywhere quantifier is explicit; this is Lean's notation ∀ᵐ with volume. Real angles give the periodic lift of the circuit parameters. Each Pauli-word rotation is a Clifford conjugate of a single-qubit Pauli rotation, so the ordered product is a parametrized quantum circuit with fifteen independent inputs.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Describe.Remark(DescribeId.Create("paulicritical-analytic-zero-set"),
                H("A nonzero real-analytic function has a null zero set"),
                Disp(AnalyticZeroSetFormula()), AssessedProvenance.FromLiterature(AnalyticZeros),
                Blocks(Paragraph(Text("Mityagin, Proposition 0, p. 1: the zero set of a real-analytic function that is not identically zero on a connected open real domain has Lebesgue measure zero. Here the domain is the whole finite-dimensional real coordinate space. AnalyticOnNhd supplies real analyticity everywhere, and a point a with f(a) nonzero supplies nontriviality. The conclusion says f(x) is nonzero for volume-almost every x. It holds also in dimension zero.")))),
            Node("result", "The critical-value bound fails", Disp(new Formula.Not(Named("claim"))),
                "In increasing input order choose the words YY, IY, XX, ZY, ZX, IZ, XY, YZ, IX, XZ, ZI, YI, YX, XI, ZZ, where AB means the tensor product of the Pauli matrices A and B. Set inputs 5, 6, 7 and 10 to π/4 and all other inputs to zero; indices start at zero. At this parameter the derivative has rank fourteen. In invertible real coordinates its Pauli-coordinate matrix is diagonal with fourteen ones and one zero. The derivative of its determinant along a nonzero kernel direction is nonzero. This is the fold condition: the kernel is transverse to the critical hypersurface. A linear projection of the critical values contains a nonempty open subset of the fourteen-dimensional real space. Lipschitz monotonicity of dimH therefore gives Hausdorff dimension at least fourteen, contradicting the bound thirteen. AnalyticZeroSetNull.ae_ne_zero_of_analytic gives the almost-everywhere full-rank step: the determinant is real analytic and its nonzero directional derivative prevents it from vanishing identically. Mityagin, Proposition 0, p. 1, states that such a zero set on a connected open real domain has Lebesgue measure zero. Thus the same sequence has full derivative rank almost everywhere and violates the proposed critical-value dimension bound.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("wierichs-kottmann-killoran-2025-critical-values"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("paulicritical-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula AnalyticZeroSetFormula()
    {
        Formula n=F.Id("n"),f=F.Id("f"),a=F.Id("a"),x=F.Id("x");
        Formula space=Arrow(Fin(n),Reals());
        Formula nonzero=new Formula.Relation(At(f,a),FormulaRelationOperator.NotEqual,D(0));
        Formula premise=new Formula.Logic(Call("AnalyticOnNhd",Reals(),f,Named("Set.univ")),
            FormulaLogicOperator.And,nonzero);
        Formula volume=Typed(Named("volume"),Call("Measure",space));
        Formula conclusion=Seq(new Formula.Subscript(
            new Formula.Power(Forall,Seq(Mathrm,Grp(F.Id("m")))),volume),Sp,
            Typed(x,space),Comma,Sp,new Formula.Relation(At(f,x),FormulaRelationOperator.NotEqual,D(0)));
        return All(n,Seq(Mathbb,Grp(F.Id("N"))),All(f,Arrow(space,Reals()),All(a,space,
            new Formula.Logic(Parenthesized(premise),FormulaLogicOperator.Implies,conclusion))));
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Named(string name) => Seq(Operatorname,
        Grp(name.Split('.').SelectMany((part, index) => index == 0
            ? new Formula[] { F.Id(part) } : new Formula[] { Dot, F.Id(part) }).ToArray()));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula At(Formula function, Formula argument) => new Formula.Apply(function, [argument]);
    private static Formula Projection(Formula value, string name) => Seq(value, Dot, Named(name));
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Sp, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, body);
    private static Formula Function(Formula variable, Formula type, Formula body) =>
        Seq(Named("fun"), Sp, Typed(variable, type), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula ENNReals() => new Formula.Power(
        new Formula.Subscript(Reals(), Seq(Geq, Sp, D(0))), Infty);
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula Words() => Arrow(Fin(D(1,5)), Named("NonIdentityPauli"));
    private static Formula Smul(Formula scalar, Formula value) => Call("SMul.smul", scalar, value);
    private static Formula Rank(Formula words, Formula angles) => Call("derivativeRank", words, angles);

    private static Formula PauliFormula()
    {
        Formula p = F.Id("p");
        Formula constant = Call("Function.const", Fin(D(2)), Named("Pauli.I"));
        Formula nonidentity = new Formula.Relation(p, FormulaRelationOperator.NotEqual, Parenthesized(constant));
        Formula subtype = Seq(OpenBrace, p, Sp, Colon, Sp, Arrow(Fin(D(2)), Named("Pauli")),
            Sp, Slash, Slash, Sp, nonidentity, CloseBrace);
        return Disp(Equal(Named("NonIdentityPauli"), subtype));
    }

    private static Formula RotationFormula()
    {
        Formula p = F.Id("p"), a = F.Id("a");
        Formula half = new Formula.Fraction(a, D(2));
        Formula value = new Formula.Binary(
            Smul(Call("Real.cos", half), Typed(D(1), Named("Mat"))),
            FormulaBinaryOperator.Subtract,
            Smul(Call("Real.sin", half), Smul(Named("Complex.I"), Call("wordOp", Projection(p, "val")))));
        return Disp(All(p, Named("NonIdentityPauli"), All(a, Reals(),
            Equal(Call("rotation", p, a), value))));
    }

    private static Formula CircuitFormula()
    {
        Formula p = F.Id("P"), a = Alpha, j = F.Id("j");
        Formula factors = Call("List.ofFn", Function(j, Fin(D(1,5)),
            Call("rotation", At(p, j), At(a, j))));
        return Disp(All(p, Words(), All(a, Named("Param"),
            Equal(Call("circuit", p, a), Projection(Parenthesized(factors), "prod")))));
    }

    private static Formula RankFormula()
    {
        Formula p = F.Id("P"), a = Alpha;
        Formula derivative = Call("fderiv", Reals(), Call("circuit", p), a);
        Formula range = Call("LinearMap.range", Projection(Parenthesized(derivative), "toLinearMap"));
        return Disp(All(p, Words(), All(a, Named("Param"),
            Equal(Rank(p, a), Call("Module.finrank", Reals(), range)))));
    }

    private static Formula CriticalFormula()
    {
        Formula p = F.Id("P"), a = Alpha;
        Formula set = Seq(OpenBrace, a, Sp, Colon, Sp, Named("Param"), Sp, Mid, Sp,
            Less(Rank(p, a), D(1,5)), CloseBrace);
        return Disp(All(p, Words(), Equal(Call("critical", p), set)));
    }

    private static Formula ClaimFormula()
    {
        Formula p = F.Id("P"), a = Alpha;
        Formula volume = Typed(Named("volume"), Call("Measure", Named("Param")));
        Formula almostEverywhere = Seq(new Formula.Subscript(
            new Formula.Power(Forall, Seq(Mathrm, Grp(F.Id("m")))), volume), Sp,
            Typed(a, Named("Param")), Comma, Sp, Equal(Rank(p, a), D(1,5)));
        Formula image = Seq(Call("circuit", p), Sp, Apos, Apos, Sp, Call("critical", p));
        Formula bound = new Formula.Relation(Call("dimH", Parenthesized(image)),
            FormulaRelationOperator.LessThanOrEqual, Typed(D(1,3), ENNReals()));
        return Disp(new Formula.Logic(Named("claim"), FormulaLogicOperator.Iff,
            Parenthesized(All(p, Words(), Implies(almostEverywhere, bound)))));
    }
}
