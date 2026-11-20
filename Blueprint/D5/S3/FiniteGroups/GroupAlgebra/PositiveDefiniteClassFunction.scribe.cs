using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class PositiveDefiniteClassFunctionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/GroupAlgebra/PositiveDefiniteClassFunction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "On an arbitrary group, a class function whose kernel is positive semidefinite and whose translates span a finite-dimensional space is a combination with positive weights of the characters of finitely many pairwise inequivalent irreducible unitary representations, and the dimension of that span is the sum of the squared degrees.",
        H("Positive semidefinite class functions of finite rank"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("positive-definite-class-function-character-expansion"),
                DeclarationHandle.Create(Prefix + "exists_sum_character_of_finiteDimensional"),
                H("Character expansion of a positive semidefinite class function of finite rank"),
                StatementSource.FromAuthor(ExpansionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let G be an arbitrary group and phi a complex-valued function on G. Three hypotheses are made. "
                        + "First, the kernel whose entry at (x, y) is phi(x * y^-1) is positive semidefinite: it is Hermitian and its quadratic form is a nonnegative real number on every finitely supported vector; in the formula, of turns the function of x and y into a matrix indexed by G x G. "
                        + "Second, phi is a class function: phi(g * x * g^-1) = phi(x) for all g and x. "
                        + "Third, the sections of the kernel, the functions x maps to phi(x * y^-1) for y in G, span a finite-dimensional complex subspace of the functions on G.")),
                    Paragraph(Text(
                        "The conclusion provides a natural number m, degrees n(i) for i in Fin(m), representations rho(i) of G on the Euclidean spaces EuclideanSpace(C, Fin(n(i))) and real weights c(i), with seven properties: every rho(i) is irreducible; rho(i) and rho(j) admit no equivalence of representations when i and j are distinct; every operator rho(i)(g) preserves the norm; every c(i) is positive; phi(x) is the sum over i of c(i), regarded as a complex number, times the character of rho(i) at x; every matrix coefficient g maps to the inner product of w and rho(i)(g)(v) lies in the span of the sections; and the dimension of the span of the sections is the sum of the squares n(i)^2. "
                        + "In the displayed formula the arguments in square brackets are the instance hypotheses of the statement.")),
                    Paragraph(Text(
                        "No topology is assumed on G. If G is a topological group and phi is continuous, the representations rho(i) are continuous: each section x maps to phi(x * y^-1) is continuous, so every function in their finite-dimensional span is continuous, and by the matrix-coefficient property every matrix coefficient of rho(i) is such a function.")),
                    Paragraph(Text(
                        "The proof begins with the reproducing kernel Hilbert space H of the kernel. Its kernel functions k(y), with k(y)(x) = phi(x * y^-1), span a dense subspace; evaluation identifies H injectively with a space of functions on G and carries this span onto the span of the sections, which is finite-dimensional, so the span is closed and equals H. "
                        + "Right translation, which sends a function h to x maps to h(x * g), maps k(y) to k(y * g^-1) and preserves the inner products of kernel functions because the kernel is invariant under right translation; it is therefore a representation pi of G on H by isometries, and the reproducing property gives phi(x) as the inner product of k(1) and pi(x)(k(1)).")),
                    Paragraph(Text(
                        "A finite-dimensional representation by isometries is semisimple "),
                        Ref("D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.isSemisimpleRepresentation_of_norm_map"),
                        Text(
                        ". By strong induction on the dimension, splitting off a proper subrepresentation and a complement, every coefficient x maps to f(pi(x)(u)) with f linear is a finite sum of trace coefficients x maps to the trace of rho(j)(x) composed with B(j), for irreducible representations rho(j) by isometries on Euclidean spaces; an irreducible summand is carried to a Euclidean space by an orthonormal basis, and its coefficient f(pi(x)(u)) is the trace of pi(x) composed with the rank-one map w maps to f(w) u. "
                        + "Equivalent representations are then grouped, conjugating the operators B(j) into one representative of each class, so that the family becomes pairwise inequivalent.")),
                    Paragraph(Text(
                        "Because phi is a class function, the difference of the trace sums at g * x * g^-1 and at x vanishes, so the families (rho(j)(g^-1) B(j) rho(j)(g) - B(j))_j pair to zero with every family (rho(j)(x))_j under the trace pairing with unit weights. "
                        + "By Burnside's theorem for the family these span the product of the endomorphism algebras "),
                        Ref("D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.span_range_pi_eq_top"),
                        Text(", and the trace pairing is nondegenerate "),
                        Ref("D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.eq_zero_of_tracePairing"),
                        Text(
                        ", so every B(j) commutes with rho(j). By Schur's lemma over the complex numbers B(j) is a scalar c(j), and phi is the sum of the c(j) times the characters. "
                        + "Since the kernel of phi is positive semidefinite, every c(j) is nonnegative "),
                        Ref("D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.posSemidef_sum_character_kernel_iff"),
                        Text(
                        ", and the representations with c(j) = 0 are dropped.")),
                    Paragraph(Text(
                        "Writing the character of rho(i) at x * y^-1 as the trace of rho(i)(x) composed with rho(i)(y^-1), the sections are the images of the families (rho(i)(y^-1))_i under the linear map that sends a family A to the function x maps to the sum over i of c(i) times the trace of rho(i)(x) composed with A(i). "
                        + "By Burnside's theorem for the family, the span of the sections is the image of the whole product of the endomorphism algebras; choosing the family that is a multiple of the rank-one map z maps to the inner product of w and z times v in position i and zero elsewhere shows that every matrix coefficient lies in that span. "
                        + "The dimension formula is the rank of a weighted character kernel "),
                        Ref("D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.finrank_span_sum_character_kernel"),
                        Text(".")),
                    Paragraph(Text(
                        "No hypothesis can be dropped. On the integers, phi(n) = n is a class function whose sections are spanned by the constant function and the identity, but its kernel x - y is not Hermitian, and phi is unbounded while every combination of characters of finite-dimensional unitary representations is bounded. "
                        + "On the group SU(2) regarded as an abstract group, a diagonal matrix coefficient of the defining representation has a positive semidefinite kernel whose sections span a space of dimension two, but it is not a class function, and two is not a sum of squared degrees of pairwise inequivalent irreducible representations, because SU(2) is perfect and its only one-dimensional representation is trivial. "
                        + "On the integers, the indicator function of 0 is a positive semidefinite class function, its kernel being the identity matrix, but its sections are the indicator functions of single points and span an infinite-dimensional space. "
                        + "These examples are not part of the formal statement.")),
                    Paragraph(Text(
                        "The result is the finite-rank case of the classical theory of functions of positive type on groups: a positive definite function whose associated cyclic representation is finite-dimensional, and which is invariant under conjugation, is a positive combination of irreducible characters. "
                        + "The statement here is for an arbitrary group, without topology, and includes the rank formula."))),
                DescribeRole.Theorem))));

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula OpApp(string name, params Formula[] arguments) => App(Op(name), arguments);
    private static Formula Inst(Formula content) => Seq(OpenBracket, content, CloseBracket, Comma, Sp);
    private static Formula Parenthesized(Formula content) => Seq(Open, content, Close);
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));

    /// <summary>A binder written with a symbol, rendered like a Bind node.</summary>
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, SemiSpace, Sp, body);

    private static Formula Some(Formula variable, Formula domain, Formula body) =>
        Seq(Exists, Sp, variable, Sp, InMacro, Sp, domain, Comma, SemiSpace, Sp, body);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula ExistsOf(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Inverse(Formula x) => new Formula.Power(x, Seq(Minus, D(1)));

    private static Formula ExpansionFormula()
    {
        Formula G = F.Id("G"), m = F.Id("m"), n = F.Id("n"), c = F.Id("c");
        Formula i = F.Id("i"), j = F.Id("j"), g = F.Id("g"), x = F.Id("x"), y = F.Id("y");
        Formula v = F.Id("v"), w = F.Id("w");
        Formula phiAt(Formula argument) => App(Varphi, argument);
        Formula rhoOf(Formula index) => App(Rho, index);
        Formula index = OpApp("Fin", m);
        Formula space = OpApp("EuclideanSpace", Complexes, OpApp("Fin", App(n, i)));

        Formula kernelBody = phiAt(Mul(x, Inverse(y)));
        Formula sections = Seq(y, Sp, Mapsto, Sp, Parenthesized(Seq(x, Sp, Mapsto, Sp, kernelBody)));
        Formula span = OpApp("span", Complexes, OpApp("range", sections));
        Formula SumOverIndex(Formula body) =>
            Seq(new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, index)), Sp, body);

        Formula positive = OpApp("PosSemidef",
            OpApp("of", Seq(x, Sp, Mapsto, Sp, Parenthesized(Seq(y, Sp, Mapsto, Sp, kernelBody)))));
        Formula classFunction = Parenthesized(ForAll("g", G, ForAll("x", G,
            Equal(phiAt(Mul(Mul(g, x), Inverse(g))), phiAt(x)))));
        Formula finite = OpApp("FiniteDimensional", Complexes, span);

        Formula irreducible = Parenthesized(ForAll("i", index, OpApp("IsIrreducible", rhoOf(i))));
        Formula inequivalent = Parenthesized(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("i"), index),
                new Formula.BoundVariable(FormulaIdentifier.Create("j"), index)],
            Implies(new Formula.Relation(i, FormulaRelationOperator.NotEqual, j),
                OpApp("IsEmpty", OpApp("Equiv", rhoOf(i), rhoOf(j))))));
        Formula isometric = Parenthesized(ForAll("i", index, ForAll("g", G, ForAll("v", space,
            Equal(new Formula.Norm(App(App(rhoOf(i), g), v)), new Formula.Norm(v))))));
        Formula weights = Parenthesized(ForAll("i", index,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThan, App(c, i))));
        Formula expansion = Parenthesized(ForAll("x", G, Equal(phiAt(x),
            SumOverIndex(Mul(App(c, i), OpApp("character", rhoOf(i), x))))));
        Formula coefficient = Seq(g, Sp, Mapsto, Sp,
            Seq(Langle, Sp, w, Comma, Sp, App(App(rhoOf(i), g), v), Sp, Rangle));
        Formula coefficients = Parenthesized(ForAll("i", index, ForAll("v", space, ForAll("w", space,
            new Formula.Relation(Parenthesized(coefficient), FormulaRelationOperator.MemberOf, span)))));
        Formula rank = Equal(OpApp("finrank", Complexes, span),
            SumOverIndex(new Formula.Power(App(n, i), D(2))));

        Formula conjunction = And(irreducible, And(inequivalent, And(isometric, And(weights,
            And(expansion, And(coefficients, rank))))));
        Formula representations = Parenthesized(ForAll("i", index,
            OpApp("Representation", Complexes, G, space)));
        Formula conclusion = ExistsOf("m", Naturals,
            ExistsOf("n", new Formula.TypeArrow(index, Naturals),
                Some(Rho, representations,
                    ExistsOf("c", new Formula.TypeArrow(index, Reals), conjunction))));

        return Disp(ForAll("G", TypeStar, Seq(
            Inst(OpApp("Group", G)),
            All(Varphi, new Formula.TypeArrow(G, Complexes),
                Implies(positive, Implies(classFunction, Implies(finite, conclusion)))))));
    }
}
