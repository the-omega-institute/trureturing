using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.GroupAlgebra;

internal sealed class CharacterKernelRankDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/GroupAlgebra/CharacterKernelRank.";
    private static LibraryNoteRef Burnside => LibraryNoteRef.Create("D5/L/FiniteGroups/burnside1905reducibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Over an algebraically closed field, a sum with nonzero weights of the characters of finitely many pairwise inequivalent finite-dimensional irreducible representations of a group gives a kernel whose rank is the sum of the squared dimensions.",
        H("Rank of a character kernel"),
        Blocks(
            Node("span-range-pi-eq-top", "span_range_pi_eq_top", "The operators of a family of irreducible representations span",
                StatementSource.FromAuthor(SpanFormula()), AssessedProvenance.FromRepo(Burnside), DescribeRole.Theorem,
                "Let k be an algebraically closed field, G a group and iota a finite index type, and for each i let rho(i) be an irreducible representation of G on a finite-dimensional k-vector space W(i), with rho(i) and rho(j) admitting no equivalence of representations when i and j are distinct. "
                    + "Then the families (rho(i)(g))_i, as g ranges over G, span the whole product over i of the endomorphism algebras End(W(i)). "
                    + "This is Burnside's theorem for a finite family. The product of the W(i) is a semisimple module over the group algebra k[G]; by Schur's lemma, with algebraic closedness and pairwise inequivalence, every k[G]-endomorphism of it acts on each factor W(i) by a scalar. "
                    + "The Jacobson density theorem for this semisimple module then shows that every family of endomorphisms is the action of an element of k[G], that is, a linear combination of the families (rho(i)(g))_i."),
            Node("trace-pairing", "tracePairing", "The weighted trace pairing",
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), DescribeRole.Definition,
                "For a field k, a finite index type iota, finite-dimensional k-vector spaces W(i) and weights c(i) in k, the weighted trace pairing is the bilinear form on the product over i of End(W(i)) that pairs the families B and A to the sum over i of c(i) times the trace of the composite B(i) A(i). "
                    + "It is linear in each argument because the trace and composition are."),
            Node("eq-zero-of-trace-pairing", "eq_zero_of_tracePairing", "The weighted trace pairing is nondegenerate",
                StatementSource.FromAuthor(PairingFormula()), AssessedProvenance.FromRepo(), DescribeRole.Lemma,
                "Let every weight c(i) be nonzero. If a family A of endomorphisms pairs to zero with every family B under the weighted trace pairing, then A is zero. "
                    + "No algebraic closedness is needed. Suppose A(j) is nonzero for some j; choose a vector v of W(j) and a linear functional f on W(j) with f(A(j) v) nonzero. "
                    + "Let B be the family that is the rank-one map w maps to f(w) v in position j and zero elsewhere. "
                    + "The pairing of B with A is c(j) times the trace of w maps to f(A(j) w) v, which is c(j) f(A(j) v), and it is nonzero."),
            Describe.Lean(
            DescribeId.Create("character-kernel-rank-finrank-span-sum-character-kernel"),
            DeclarationHandle.Create(Prefix + "finrank_span_sum_character_kernel"),
            H("The rank of a weighted character kernel"),
            StatementSource.FromAuthor(RankFormula()),
            AssessedProvenance.FromRepo(Burnside),
            Blocks(
                Paragraph(Text(
                    "Let k be an algebraically closed field, G an arbitrary group and iota a finite index type. For each index i, rho(i) is a representation of G on a finite-dimensional k-vector space W(i); every rho(i) is irreducible, and rho(i) and rho(j) admit no equivalence of representations when i and j are distinct. "
                    + "Let c(i) be nonzero scalars. For y in G, the section of the kernel at y is the function on G sending x to the sum over i of c(i) times the character of rho(i) at x * y^-1. "
                    + "The statement is that these sections, as y ranges over G, span a subspace of the space of functions from G to k whose dimension is the sum over i of dim W(i)^2. "
                    + "In the displayed formula the arguments in square brackets are the instance hypotheses of the statement. "
                    + "Nothing beyond the group axioms is assumed about G: it may be infinite, and no topology or measure enters.")),
                Paragraph(Text(
                    "The sections are images of one linear map. Send a family A of endomorphisms, A(i) in End(W(i)), to the function on G whose value at x is the sum over i of c(i) times the trace of rho(i)(x) composed with A(i). "
                    + "Since the character of rho(i) at x * y^-1 is the trace of rho(i)(x) composed with rho(i)(y^-1), the section at y is the image of the family (rho(i)(y^-1))_i. "
                    + "Inversion is a bijection of G, so the span of the sections is the image of the span of the families (rho(i)(g))_i for g in G.")),
                Paragraph(Text(
                    "That span is the whole product of the endomorphism algebras End(W(i)). This is Burnside's theorem for a finite family: the product of the W(i) is a semisimple module over the group algebra k[G] whose simple summands are pairwise non-isomorphic, so by Schur's lemma every k[G]-endomorphism of the product acts on each factor by a scalar, and the Jacobson density theorem then shows that the group algebra maps onto the product of the endomorphism algebras. "
                    + "For a single irreducible representation this surjectivity is the theorem "),
                    Ref("D5/S3/FiniteGroups/FiniteCharacterAlgebra.asAlgebraHom_surjective_of_isIrreducible"),
                    Text("; the family version is proved here from the density theorem on the product module rather than from that statement.")),
                Paragraph(Text(
                    "The linear map is injective because the weighted trace pairing, which pairs families B and A to the sum over i of c(i) times the trace of B(i) composed with A(i), is nondegenerate when every c(i) is nonzero: for A(j) nonzero, choose a vector v and a linear functional f with f(A(j) v) nonzero, and pair A with the family that is the rank-one map w maps to f(w) v in position j and zero elsewhere. "
                    + "Hence the span of the sections has the dimension of the product of the End(W(i)), which is the sum of dim W(i)^2.")),
                Paragraph(Text(
                    "Algebraic closedness enters only through Schur's lemma: the same argument applies whenever every k[G]-endomorphism of each W(i) is a scalar. It cannot simply be dropped. "
                    + "Over the real numbers, the rotation representation of the circle group on the plane is irreducible of dimension two, but its character at the rotation by t is 2 cos t, and the sections of c times 2 cos(s - t) are spanned by cos and sin, so the rank is two rather than four. "
                    + "Irreducibility cannot be dropped: the trivial action of any group on k^2 has the constant character 2, so its kernel has rank at most one rather than four. "
                    + "Pairwise inequivalence cannot be dropped: two copies of the trivial representation on k with weights c(1) and c(2) give the constant kernel c(1) + c(2), of rank at most one rather than two; the rank is zero for the weights 1 and -1 in every characteristic, and for the weights 1 and 1 in characteristic two.")),
                Paragraph(Text(
                    "For one representation the statement is Burnside's theorem read through the nondegenerate trace pairing; for several it is the same reading for a semisimple module with pairwise non-isomorphic simple summands."))),
            DescribeRole.Theorem))));

    private static DocumentBlock Node(
        string id, string selector, string title, StatementSource statement,
        AssessedProvenance provenance, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create("character-kernel-rank-" + id),
            DeclarationHandle.Create(Prefix + selector), H(title), statement, provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula ProdOverIndex(Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(F.Id("i"), Sp, InMacro, Sp, IndexType)), Sp, body);

    /// <summary>The product over i of the endomorphism algebras End(W(i)).</summary>
    private static Formula Endomorphisms(Formula k) => ProdOverIndex(OpApp("End", k, App(F.Id("W"), F.Id("i"))));

    /// <summary>The instance hypotheses on the spaces W(i), followed by the body.</summary>
    private static Formula OverSpaces(Formula k, Formula body)
    {
        Formula Wi = App(F.Id("W"), F.Id("i"));
        return ForAll("W", new Formula.TypeArrow(IndexType, TypeStar), Seq(
            Inst(ForAll("i", IndexType, OpApp("AddCommGroup", Wi))),
            Inst(ForAll("i", IndexType, OpApp("Module", k, Wi))),
            Inst(ForAll("i", IndexType, OpApp("FiniteDimensional", k, Wi))),
            body));
    }

    private static Formula SpanFormula()
    {
        Formula k = F.Id("k"), G = F.Id("G"), W = F.Id("W"), i = F.Id("i"), j = F.Id("j"), g = F.Id("g");
        Formula rhoOf(Formula index) => App(Rho, index);
        Formula families = Seq(g, Sp, Mapsto, Sp, Parenthesized(Seq(i, Sp, Mapsto, Sp, App(rhoOf(i), g))));
        Formula conclusion = new Formula.Relation(OpApp("span", k, OpApp("range", families)),
            FormulaRelationOperator.Equal, Endomorphisms(k));
        Formula inequivalent = Parenthesized(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("i"), IndexType),
                new Formula.BoundVariable(FormulaIdentifier.Create("j"), IndexType)],
            Implies(new Formula.Relation(i, FormulaRelationOperator.NotEqual, j),
                OpApp("IsEmpty", OpApp("Equiv", rhoOf(i), rhoOf(j))))));
        Formula afterRho = Seq(
            Inst(ForAll("i", IndexType, OpApp("IsIrreducible", rhoOf(i)))),
            Implies(inequivalent, conclusion));
        Formula body = All(Rho, Parenthesized(ForAll("i", IndexType, OpApp("Representation", k, G, App(W, i)))), afterRho);
        return Disp(ForAll("k", TypeStar, ForAll("G", TypeStar, Seq(
            Inst(OpApp("Field", k)), Inst(OpApp("IsAlgClosed", k)), Inst(OpApp("Group", G)),
            All(IndexType, TypeStar, Seq(Inst(OpApp("Fintype", IndexType)), OverSpaces(k, body)))))));
    }

    private static Formula PairingFormula()
    {
        Formula k = F.Id("k"), c = F.Id("c"), i = F.Id("i"), A = F.Id("A"), B = F.Id("B");
        Formula nonzero = Parenthesized(ForAll("i", IndexType,
            new Formula.Relation(App(c, i), FormulaRelationOperator.NotEqual, D(0))));
        Formula orthogonal = Parenthesized(ForAll("B", Endomorphisms(k),
            new Formula.Relation(OpApp("tracePairing", c, B, A), FormulaRelationOperator.Equal, D(0))));
        Formula body = ForAll("c", new Formula.TypeArrow(IndexType, k), Implies(nonzero,
            ForAll("A", Endomorphisms(k), Implies(orthogonal,
                new Formula.Relation(A, FormulaRelationOperator.Equal, D(0))))));
        return Disp(ForAll("k", TypeStar, Seq(
            Inst(OpApp("Field", k)),
            All(IndexType, TypeStar, Seq(Inst(OpApp("Fintype", IndexType)), OverSpaces(k, body))))));
    }

    private static Formula Op(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula OpApp(string name, params Formula[] arguments) => App(Op(name), arguments);
    private static Formula Inst(Formula content) => Seq(OpenBracket, content, CloseBracket, Comma, Sp);
    private static Formula Parenthesized(Formula content) => Seq(Open, content, Close);
    private static Formula TypeStar => Seq(Operatorname, Grp(F.Id("Type")), Star);
    private static Formula IndexType => Seq(Iota);

    /// <summary>A universal binder written with a symbol, rendered like a Bind node.</summary>
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, SemiSpace, Sp, body);

    private static Formula ForAll(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula SumOverIndex(Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id("i"), Sp, InMacro, Sp, IndexType)), Sp, body);

    private static Formula RankFormula()
    {
        Formula k = F.Id("k"), G = F.Id("G"), W = F.Id("W"), c = F.Id("c");
        Formula i = F.Id("i"), j = F.Id("j"), x = F.Id("x"), y = F.Id("y");
        Formula Wi = App(W, i);
        Formula rhoOf(Formula index) => App(Rho, index);

        Formula summand = new Formula.Binary(App(c, i), FormulaBinaryOperator.Multiply,
            OpApp("character", rhoOf(i),
                new Formula.Binary(x, FormulaBinaryOperator.Multiply, new Formula.Power(y, Seq(Minus, D(1))))));
        Formula section = Seq(y, Sp, Mapsto, Sp, Parenthesized(Seq(x, Sp, Mapsto, Sp, SumOverIndex(summand))));
        Formula left = OpApp("finrank", k, OpApp("span", k, OpApp("range", section)));
        Formula right = SumOverIndex(new Formula.Power(OpApp("finrank", k, Wi), D(2)));
        Formula conclusion = new Formula.Relation(left, FormulaRelationOperator.Equal, right);

        Formula inequivalent = Parenthesized(new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("i"), IndexType),
                new Formula.BoundVariable(FormulaIdentifier.Create("j"), IndexType)],
            Implies(new Formula.Relation(i, FormulaRelationOperator.NotEqual, j),
                OpApp("IsEmpty", OpApp("Equiv", rhoOf(i), rhoOf(j))))));
        Formula nonzero = Parenthesized(ForAll("i", IndexType,
            new Formula.Relation(App(c, i), FormulaRelationOperator.NotEqual, D(0))));
        Formula afterRho = Seq(
            Inst(ForAll("i", IndexType, OpApp("IsIrreducible", rhoOf(i)))),
            Implies(inequivalent,
                ForAll("c", new Formula.TypeArrow(IndexType, k), Implies(nonzero, conclusion))));

        Formula familyBody = Seq(
            Inst(ForAll("i", IndexType, OpApp("AddCommGroup", Wi))),
            Inst(ForAll("i", IndexType, OpApp("Module", k, Wi))),
            Inst(ForAll("i", IndexType, OpApp("FiniteDimensional", k, Wi))),
            All(Rho, Parenthesized(ForAll("i", IndexType, OpApp("Representation", k, G, Wi))), afterRho));

        return Disp(ForAll("k", TypeStar, ForAll("G", TypeStar, Seq(
            Inst(OpApp("Field", k)), Inst(OpApp("IsAlgClosed", k)), Inst(OpApp("Group", G)),
            All(IndexType, TypeStar, Seq(
                Inst(OpApp("Fintype", IndexType)),
                ForAll("W", new Formula.TypeArrow(IndexType, TypeStar), familyBody)))))));
    }
}
