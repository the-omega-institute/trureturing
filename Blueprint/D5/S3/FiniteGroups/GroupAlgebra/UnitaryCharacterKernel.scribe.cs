using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class UnitaryCharacterKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.";
    private static LibraryNoteRef Folland => LibraryNoteRef.Create("D5/L/Fourier/folland2016course");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A representation of a monoid by isometries of a finite-dimensional real or complex inner product space is semisimple; a weighted sum of the characters of finitely many representations of a group by isometries is a positive semidefinite kernel when every weight is nonnegative, and for pairwise inequivalent irreducible representations exactly when every weight is nonnegative.",
        H("Unitary representations and positivity of character kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("unitary-character-kernel-semisimple"),
                DeclarationHandle.Create(Prefix + "isSemisimpleRepresentation_of_norm_map"),
                H("Representations by isometries are semisimple"),
                StatementSource.FromAuthor(SemisimpleFormula()),
                AssessedProvenance.FromRepo(Folland),
                Blocks(
                    Paragraph(Text(
                        "Let k be the field of real or of complex numbers (an RCLike field), G an arbitrary monoid and E a finite-dimensional inner product space over k. "
                        + "Let rho be a representation of G on E such that every operator rho(g) preserves the norm: the norm of rho(g)(v) equals the norm of v for all g in G and v in E. "
                        + "The statement is that rho is semisimple, that is, every subrepresentation of rho has a complementary subrepresentation. "
                        + "In the displayed formula the arguments in square brackets are the instance hypotheses of the statement. "
                        + "Nothing beyond the monoid axioms is assumed about G: it need not have inverses, it may be infinite, and no topology enters.")),
                    Paragraph(Text(
                        "Let S be a subrepresentation and let T be the orthogonal complement of its underlying subspace. Fix g in G and write U for rho(g). "
                        + "A linear map that preserves the norm is injective and, by polarization, preserves the inner product. "
                        + "U maps S into S, and its image of S has the dimension of S because U is injective, so in finite dimension U maps S onto S. "
                        + "If v is orthogonal to S and w lies in S, write w = U(w0) with w0 in S; then the inner product of w and U(v) equals the inner product of w0 and v, which is zero. "
                        + "Hence T is invariant under every rho(g) and is a subrepresentation; no inverse in G is used. "
                        + "Because E is finite-dimensional, S and its orthogonal complement are complementary subspaces, so T is a complement of S in the lattice of subrepresentations.")),
                    Paragraph(Text(
                        "This is the classical complete reducibility of unitary representations. "
                        + "The isometry hypothesis cannot be dropped: the additive group of the integers acting on the plane by n maps (a, b) to (a + n b, b) leaves the line b = 0 invariant, and that line has no invariant complement, since an invariant line spanned by (x, 1) would be mapped to the line spanned by (x + 1, 1).")),
                    Paragraph(Text(
                        "The statement is used in the decomposition of finite-dimensional unitary representations into irreducible ones: by induction on the dimension, a proper subrepresentation and a complement of it are split off until every summand is irreducible."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-character-kernel-nonnegative-weights"),
                DeclarationHandle.Create(Prefix + "posSemidef_sum_character_kernel_of_nonneg"),
                H("Character kernels with nonnegative weights are positive semidefinite"),
                StatementSource.FromAuthor(NonnegFormula()),
                AssessedProvenance.FromRepo(Folland),
                Blocks(
                    Paragraph(Text(
                        "Let G be an arbitrary group and iota a finite index type. For each index i, W(i) is a finite-dimensional complex inner product space and rho(i) is a representation of G on W(i) whose operators preserve the norm; no irreducibility and no inequivalence is assumed. "
                        + "Let c(i) be complex weights with 0 <= c(i), where the order on the complex numbers is the one in which a is at most b exactly when b - a is a nonnegative real number. "
                        + "The statement is that the matrix indexed by G x G whose entry at (x, y) is the sum over i of c(i) times the character of rho(i) at x * y^-1 is positive semidefinite: it is Hermitian and its quadratic form is a nonnegative real number on every finitely supported vector. "
                        + "In the formula, of turns this function of x and y into a matrix, and the arguments in square brackets are the instance hypotheses of the statement.")),
                    Paragraph(Text(
                        "Choose an orthonormal basis e(1), ..., e(d) of each W(i). Since rho(i)(x^-1) preserves the inner product, the character of rho(i) at x * y^-1, which is the trace of rho(i)(x) composed with rho(i)(y^-1), equals the sum over k of the inner products of rho(i)(x^-1)(e(k)) and rho(i)(y^-1)(e(k)). "
                        + "Each such term, as a function of x and y, is the Gram kernel of the vectors rho(i)(x^-1)(e(k)) indexed by x in G, and a Gram kernel indexed by an arbitrary type is positive semidefinite because its quadratic form at a finitely supported vector a is the squared norm of the sum of the a(x) times the corresponding vectors. "
                        + "A combination of positive semidefinite kernels with nonnegative weights is positive semidefinite.")),
                    Paragraph(Text(
                        "Positivity of the characters of unitary representations is classical in harmonic analysis on groups; the statement here is for an arbitrary group, with no topology, and for a finite family of representations that need not be irreducible."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("unitary-character-kernel-positive-semidefinite"),
                DeclarationHandle.Create(Prefix + "posSemidef_sum_character_kernel_iff"),
                H("Positive semidefinite character kernels"),
                StatementSource.FromAuthor(PositivityFormula()),
                AssessedProvenance.FromRepo(Folland),
                Blocks(
                    Paragraph(Text(
                        "Let G be an arbitrary group and iota a finite index type. For each index i, W(i) is a finite-dimensional complex inner product space and rho(i) is an irreducible representation of G on W(i) whose operators preserve the norm; rho(i) and rho(j) admit no equivalence of representations when i and j are distinct. "
                        + "Let c(i) be complex weights. The kernel is the matrix indexed by G x G whose entry at (x, y) is the sum over i of c(i) times the character of rho(i) at x * y^-1; in the formula, of turns this function of x and y into a matrix. "
                        + "A matrix indexed by an arbitrary type is positive semidefinite when it is Hermitian and its quadratic form is a nonnegative real number on every finitely supported vector. "
                        + "The statement is that the kernel is positive semidefinite if and only if every weight c(i) is nonnegative; the order on the complex numbers is the one in which a is at most b exactly when b - a is a nonnegative real number. "
                        + "In the displayed formula the arguments in square brackets are the instance hypotheses of the statement.")),
                    Paragraph(Text(
                        "For nonnegative weights the kernel is positive semidefinite by the preceding theorem, which needs neither irreducibility nor inequivalence "),
                        Ref("D5/S3/FiniteGroups/GroupAlgebra/UnitaryCharacterKernel.posSemidef_sum_character_kernel_of_nonneg"),
                        Text(".")),
                    Paragraph(Text(
                        "Conversely, suppose the kernel is positive semidefinite and fix an index i. "
                        + "By Burnside's theorem for the family, the families (rho(j)(g))_j, as g ranges over G, span the whole product of the endomorphism algebras End(W(j)) "),
                        Ref("D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.span_range_pi_eq_top"),
                        Text(
                        ", and inversion is a bijection of G, so there is a finitely supported function b on G for which the sum over y of b(y) times (rho(j)(y^-1))_j is the family that is the identity on W(i) and zero on every other W(j). "
                        + "Because every rho(j)(g) preserves the inner product, its adjoint is rho(j)(g^-1), so the sum over x of the complex conjugate of b(x) times (rho(j)(x))_j is the adjoint family, which is the same family. "
                        + "Expanding the quadratic form of the kernel at b gives the weighted trace pairing of these two families, which is c(i) times the dimension of W(i). "
                        + "An irreducible representation is nonzero, so this dimension is positive and c(i) is nonnegative.")),
                    Paragraph(Text(
                        "The direction from nonnegative weights to positivity holds for representations by isometries without irreducibility or inequivalence. "
                        + "The converse needs both. On the symmetric group of order two, with sign the nontrivial one-dimensional representation, the reducible representation trivial plus sign and the trivial representation, with weights 1 and -1, give the kernel sign(x) sign(y), which is positive semidefinite although one weight is negative. "
                        + "Two copies of the trivial representation with weights 1 and -1 give the zero kernel. "
                        + "These two examples are not part of the formal statement.")),
                    Paragraph(Text(
                        "Positivity of characters of unitary representations is classical in harmonic analysis on groups. The converse rests on Burnside's theorem for the family and on the weighted trace pairing; the statement here is for an arbitrary group, with no topology, and for a finite family."))),
                DescribeRole.Theorem))));

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula OpApp(string name, params Formula[] arguments) => App(Op(name), arguments);
    private static Formula Inst(Formula content) => Seq(OpenBracket, content, CloseBracket, Comma, Sp);
    private static Formula Parenthesized(Formula content) => Seq(Open, content, Close);
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula IndexType => Seq(Iota);
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));

    /// <summary>A universal binder written with a symbol, rendered like a Bind node.</summary>
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, SemiSpace, Sp, body);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula SumOverIndex(Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, InMacro, Sp, IndexType)), Sp, body);

    /// <summary>The isometry hypothesis for an operator family applied as op(g)(v).</summary>
    private static Formula Isometric(Formula op, Formula space) =>
        ForAll("g", F.Id("G"), ForAll("v", space,
            Equal(new Formula.Norm(App(App(op, F.Id("g")), F.Id("v"))), new Formula.Norm(F.Id("v")))));

    private static Formula SemisimpleFormula()
    {
        Formula k = F.Id("k"), G = F.Id("G"), E = F.Id("E");
        Formula isometric = Parenthesized(Isometric(Rho, E));
        Formula body = All(Rho, OpApp("Representation", k, G, E),
            Implies(isometric, OpApp("IsSemisimpleRepresentation", Rho)));
        return Disp(ForAll("k", TypeStar, ForAll("G", TypeStar, ForAll("E", TypeStar, Seq(
            Inst(OpApp("RCLike", k)), Inst(OpApp("Monoid", G)), Inst(OpApp("NormedAddCommGroup", E)),
            Inst(OpApp("InnerProductSpace", k, E)), Inst(OpApp("FiniteDimensional", k, E)),
            body)))));
    }

    private static Formula NonnegFormula()
    {
        Formula G = F.Id("G"), W = F.Id("W"), c = F.Id("c");
        Formula i = F.Id("i"), x = F.Id("x"), y = F.Id("y");
        Formula Wi = App(W, i);
        Formula rhoOf(Formula index) => App(Rho, index);

        Formula summand = new Formula.Binary(App(c, i), FormulaBinaryOperator.Multiply,
            OpApp("character", rhoOf(i),
                new Formula.Binary(x, FormulaBinaryOperator.Multiply, new Formula.Power(y, Seq(Minus, D(1))))));
        Formula kernel = OpApp("of", Seq(x, Sp, Mapsto, Sp, Parenthesized(Seq(y, Sp, Mapsto, Sp, SumOverIndex(summand)))));
        Formula nonnegative = Parenthesized(ForAll("i", IndexType,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, App(c, i))));
        Formula conclusion = ForAll("c", new Formula.TypeArrow(IndexType, Complexes),
            Implies(nonnegative, OpApp("PosSemidef", kernel)));
        Formula isometric = Parenthesized(ForAll("i", IndexType, Isometric(rhoOf(i), Wi)));

        Formula familyBody = Seq(
            Inst(ForAll("i", IndexType, OpApp("NormedAddCommGroup", Wi))),
            Inst(ForAll("i", IndexType, OpApp("InnerProductSpace", Complexes, Wi))),
            Inst(ForAll("i", IndexType, OpApp("FiniteDimensional", Complexes, Wi))),
            All(Rho, Parenthesized(ForAll("i", IndexType, OpApp("Representation", Complexes, G, Wi))),
                Implies(isometric, conclusion)));

        return Disp(ForAll("G", TypeStar, Seq(
            Inst(OpApp("Group", G)),
            All(IndexType, TypeStar, Seq(
                Inst(OpApp("Fintype", IndexType)),
                ForAll("W", new Formula.TypeArrow(IndexType, TypeStar), familyBody))))));
    }

    private static Formula PositivityFormula()
    {
        Formula G = F.Id("G"), W = F.Id("W"), c = F.Id("c");
        Formula i = F.Id("i"), j = F.Id("j"), x = F.Id("x"), y = F.Id("y");
        Formula Wi = App(W, i);
        Formula rhoOf(Formula index) => App(Rho, index);

        Formula summand = new Formula.Binary(App(c, i), FormulaBinaryOperator.Multiply,
            OpApp("character", rhoOf(i),
                new Formula.Binary(x, FormulaBinaryOperator.Multiply, new Formula.Power(y, Seq(Minus, D(1))))));
        Formula kernel = OpApp("of", Seq(x, Sp, Mapsto, Sp, Parenthesized(Seq(y, Sp, Mapsto, Sp, SumOverIndex(summand)))));
        Formula nonnegative = Parenthesized(ForAll("i", IndexType,
            new Formula.Relation(D(0), FormulaRelationOperator.LessThanOrEqual, App(c, i))));
        Formula conclusion = ForAll("c", new Formula.TypeArrow(IndexType, Complexes),
            Iff(OpApp("PosSemidef", kernel), nonnegative));

        Formula inequivalent = Parenthesized(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("i"), IndexType),
                new Formula.BoundVariable(FormulaIdentifier.Create("j"), IndexType)],
            Implies(new Formula.Relation(i, FormulaRelationOperator.NotEqual, j),
                OpApp("IsEmpty", OpApp("Equiv", rhoOf(i), rhoOf(j))))));
        Formula isometric = Parenthesized(ForAll("i", IndexType, Isometric(rhoOf(i), Wi)));
        Formula afterRho = Seq(
            Inst(ForAll("i", IndexType, OpApp("IsIrreducible", rhoOf(i)))),
            Implies(inequivalent, Implies(isometric, conclusion)));

        Formula familyBody = Seq(
            Inst(ForAll("i", IndexType, OpApp("NormedAddCommGroup", Wi))),
            Inst(ForAll("i", IndexType, OpApp("InnerProductSpace", Complexes, Wi))),
            Inst(ForAll("i", IndexType, OpApp("FiniteDimensional", Complexes, Wi))),
            All(Rho, Parenthesized(ForAll("i", IndexType, OpApp("Representation", Complexes, G, Wi))), afterRho));

        return Disp(ForAll("G", TypeStar, Seq(
            Inst(OpApp("Group", G)),
            All(IndexType, TypeStar, Seq(
                Inst(OpApp("Fintype", IndexType)),
                ForAll("W", new Formula.TypeArrow(IndexType, TypeStar), familyBody))))));
    }
}
