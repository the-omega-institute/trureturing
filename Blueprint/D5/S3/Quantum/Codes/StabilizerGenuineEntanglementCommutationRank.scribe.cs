using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Codes;

internal sealed class StabilizerGenuineEntanglementCommutationRankDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Codes/StabilizerGenuineEntanglementCommutationRank";
    private static LibraryNoteRef Source => LibraryNoteRef.Create(
        "D5/L/QuantumContext/makutakuzakaaugusiak2023fully");

    private static Formula N => F.Id("N");
    private static Formula P => F.Id("p");
    private static Formula K => F.Id("k");
    private static Formula G => F.Id("G");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Field => Call("ZMod", P);
    private static Formula Parties => Call("Fin", N);
    private static Formula Coordinates => Arrow(Parties, Field);
    private static Formula States => Arrow(Parenthesized(Coordinates), Complexes);
    private static Formula Words => Call("PauliWord", N, P);
    private static Formula Generators => Arrow(Call("Fin", K), Words);
    private static Formula Operators => Call("Matrix", Parenthesized(Coordinates),
        Parenthesized(Coordinates), Complexes);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner), Dot, F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(variable, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaTerm(Formula variable, Formula type, Formula body) =>
        Parenthesized(Seq(Typed(variable, type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Sp, Parenthesized(body));
    private static Formula EqF(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NeF(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LeF(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula value, Formula set) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, set);
    private static Formula AndF(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Projection(Formula value, string field) => Seq(value, Dot, F.Id(field));
    private static Formula Component(Formula value, byte index) => Seq(value, Dot, D(index));
    private static Formula Complement(Formula set) => new Formula.Power(set, F.Id("c"));
    private static Formula SetOfParties => Call("Set", Parties);
    private static Formula Prime => App(Qualified("Nat", "Prime"), P);
    private static Formula OverSizes(Formula body) => All(N, Naturals, All(P, Naturals, body));
    private static Formula OverGenerators(Formula instance, Formula body) => OverSizes(
        All(K, Naturals, Instance(instance, All(G, Generators, body))));

    private static Formula WordDefinition => OverSizes(Seq(
        Named("structure"), Sp, Call("PauliWord", N, P), Colon, Sp, Named("Type"), Sp,
        Named("where"), Sp, OpenBrace,
        Typed(Named("phase"), Field), Comma, Sp,
        Typed(F.Id("x"), Parenthesized(Coordinates)), Comma, Sp,
        Typed(F.Id("z"), Parenthesized(Coordinates)), CloseBrace));

    private static Formula OperatorDefinition
    {
        get
        {
            Formula w = F.Id("w");
            Formula u = F.Id("u");
            Formula v = F.Id("v");
            Formula n = F.Id("n");
            Formula entry = Call("displacement", P,
                App(Projection(w, "x"), n), App(Projection(w, "z"), n), App(u, n), App(v, n));
            Formula product = Seq(new Formula.Subscript(Prod, Seq(n, Colon, Sp, Parties)), Sp,
                Parenthesized(entry));
            Formula matrix = App(Qualified("Matrix", "of"),
                LambdaTerm(u, Coordinates, LambdaTerm(v, Coordinates, product)));
            Formula phase = new Formula.Power(Call("windowRoot", P),
                Projection(Projection(w, "phase"), "val"));
            Formula body = Seq(Parenthesized(phase), Sp, Cdot, Sp, Parenthesized(matrix));
            return OverSizes(Instance(Call("NeZero", P), All(w, Words,
                EqF(Typed(Call("pauliWordOperator", w), Operators), body))));
        }
    }

    private static Formula CommutationDefinition
    {
        get
        {
            Formula a = F.Id("a");
            Formula b = F.Id("b");
            Formula n = F.Id("n");
            Formula value = Sub(
                Mul(App(Projection(a, "z"), n), App(Projection(b, "x"), n)),
                Mul(App(Projection(a, "x"), n), App(Projection(b, "z"), n)));
            return OverSizes(All(a, Words, All(b, Words,
                EqF(Typed(Call("commutationVector", a, b), Parenthesized(Coordinates)),
                    LambdaTerm(n, Parties, value)))));
        }
    }

    private static Formula SubspaceDefinition => OverGenerators(Call("NeZero", P),
        EqF(Typed(Call("stabilizerSubspace", G), Call("Submodule", Complexes, Parenthesized(States))),
            Call("iInf", LambdaTerm(F.Id("i"), Call("Fin", K),
                App(Qualified("LinearMap", "fixedSubmodule"),
                    Projection(Parenthesized(Call("pauliWordOperator", App(G, F.Id("i")))), "mulVecLin"))))));

    private static Formula ProductDefinition
    {
        get
        {
            Formula qSet = F.Id("Q");
            Formula q = F.Id("q");
            Formula x = F.Id("x");
            Formula u = F.Id("u");
            Formula v = F.Id("v");
            Formula qType = App(Qualified("CoeSort", "coe"), qSet);
            Formula complementType = App(Qualified("CoeSort", "coe"), Complement(qSet));
            Formula inclusion = Typed(App(Qualified("Subtype", "val"), q), Parties);
            Formula left = LambdaTerm(q, qType, App(x, inclusion));
            Formula right = LambdaTerm(q, complementType, App(x, inclusion));
            Formula body = Some(u, Arrow(Parenthesized(Arrow(qType, Field)), Complexes),
                Some(v, Arrow(Parenthesized(Arrow(complementType, Field)), Complexes),
                    All(x, Coordinates, EqF(App(Psi, x), Mul(App(u, left), App(v, right))))));
            return OverSizes(All(qSet, SetOfParties, All(Psi, States,
                EqF(Call("productAcross", qSet, Psi), Parenthesized(body)))));
        }
    }

    private static Formula EntanglementDefinition => OverGenerators(Call("NeZero", P),
        EqF(Call("genuinelyEntangled", G), Parenthesized(All(Psi, States,
            Imp(Member(Psi, Call("stabilizerSubspace", G)), Imp(NeF(Psi, Typed(D(0), States)),
                All(F.Id("Q"), SetOfParties,
                    Imp(Projection(F.Id("Q"), "Nonempty"),
                        Imp(Projection(Parenthesized(Complement(F.Id("Q"))), "Nonempty"),
                            new Formula.Not(Parenthesized(Call("productAcross", F.Id("Q"), Psi))))))))))));

    private static Formula SpaceDefinition
    {
        get
        {
            Formula ij = F.Id("ij");
            Formula pairs = Seq(Call("Fin", K), Sp, Times, Sp, Call("Fin", K));
            Formula range = App(Qualified("Set", "range"), LambdaTerm(ij, pairs,
                Call("commutationVector", App(G, Component(ij, 1)), App(G, Component(ij, 2)))));
            return OverGenerators(Call("Fact", Prime),
                EqF(Typed(Call("commutationSpace", G), Call("Submodule", Field, Parenthesized(Coordinates))),
                    App(Qualified("Submodule", "span"), Field, range)));
        }
    }

    private static Formula GeneratedDefinition => OverGenerators(Call("NeZero", P),
        EqF(Typed(Call("generatedOperators", G), Call("Submonoid", Operators)),
            App(Qualified("Submonoid", "closure"),
                App(Qualified("Set", "range"), LambdaTerm(F.Id("i"), Call("Fin", K),
                    Call("pauliWordOperator", App(G, F.Id("i"))))))));

    private static Formula StabilizerDefinition
    {
        get
        {
            Formula i = F.Id("i");
            Formula j = F.Id("j");
            Formula a = F.Id("A");
            Formula c = F.Id("c");
            Formula commuting = All(i, Call("Fin", K), All(j, Call("Fin", K),
                Call("Commute", Call("pauliWordOperator", App(G, i)), Call("pauliWordOperator", App(G, j)))));
            Formula scalar = All(a, Operators, Imp(Member(a, Call("generatedOperators", G)),
                All(c, Complexes, Imp(EqF(a, App(Qualified("Matrix", "scalar"), Parenthesized(Coordinates), c)),
                    EqF(c, Typed(D(1), Complexes))))));
            return OverGenerators(Call("NeZero", P),
                EqF(Call("IsStabilizer", G), Parenthesized(AndF(commuting, scalar))));
        }
    }

    private static Formula ClaimStatement
    {
        get
        {
            Formula hp = F.Id("hp");
            Formula numerator = new Formula.Binary(Parenthesized(Sub(N, D(1))),
                FormulaBinaryOperator.Add, Parenthesized(Sub(P, D(2))));
            Formula quotient = App(Qualified("Nat", "div"), Parenthesized(numerator), Parenthesized(Sub(P, D(1))));
            Formula primeInstance = Seq(Langle, Sp, hp, Sp, Rangle);
            Formula space = Call("commutationSpace", N, P, K, primeInstance, G);
            Formula rank = App(Qualified("Module", "finrank"), Field,
                App(Qualified("CoeSort", "coe"), space));
            return OverSizes(All(K, Naturals, Imp(LeF(D(1), N), All(hp, Prime,
                All(G, Generators, Imp(Call("IsStabilizer", G),
                    Imp(Call("genuinelyEntangled", G), LeF(quotient, rank))))))));
        }
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Genuine entanglement forces a lower bound on the dimension of the Pauli commutation space over a prime field.",
        H("Genuine entanglement and commutation rank"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("pauli-word"), DeclarationHandle.Create(Module + ".PauliWord"),
                H("Pauli word coordinates"), StatementSource.FromAuthor(Disp(WordDefinition)),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "A PauliWord has a phase residue and two functions x and z assigning residues to the N parties. "
                    + "This is a record of coordinates, with no multiplication imposed on the record itself. "
                    + "The parameters N and p are arbitrary natural numbers."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("pauli-word-operator"), DeclarationHandle.Create(Module + ".pauliWordOperator"),
                H("The matrix of a Pauli word"), StatementSource.FromAuthor(Disp(OperatorDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For nonzero p, the matrix is the phase windowRoot(p) raised to the natural representative "
                    + "w.phase.val, multiplying the tensor product of the local displacements X to the power "
                    + "w.x(n) followed by Z to the power w.z(n). The product gives its entries in the basis "
                    + "indexed by functions from Fin N to ZMod p. The dot denotes complex scalar multiplication "
                    + "of a matrix. See final_5.tex, lines 190–196 and 215–216."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("commutation-vector"), DeclarationHandle.Create(Module + ".commutationVector"),
                H("Local commutation phases"), StatementSource.FromAuthor(Disp(CommutationDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "At party n the commutation exponent is a.z(n)b.x(n) minus a.x(n)b.z(n), computed in ZMod p. "
                    + "Thus the global phases of a and b do not affect this vector. This is the coordinate "
                    + "form of the local commutation exponents in final_5.tex, lines 375–382."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("stabilizer-subspace"), DeclarationHandle.Create(Module + ".stabilizerSubspace"),
                H("The common fixed subspace"), StatementSource.FromAuthor(Disp(SubspaceDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Intersect the fixed submodules of the matrix actions of all generators. "
                    + "A vector belongs precisely when every generator fixes it; the same then holds for "
                    + "every finite product of generators. The intersection iInf is indexed by i in Fin k. "
                    + "See final_5.tex, lines 224–230."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("product-across"), DeclarationHandle.Create(Module + ".productAcross"),
                H("Factorization across a bipartition"), StatementSource.FromAuthor(Disp(ProductDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A vector factors across Q when its amplitude at every configuration x is the product "
                    + "of one amplitude u depending only on the Q coordinates and one amplitude v depending "
                    + "only on the complementary coordinates. CoeSort.coe makes the subtype belonging to "
                    + "a set explicit, and Subtype.val(q) is its inclusion into Fin N. No nonzero or "
                    + "normalization condition is imposed here. See final_5.tex, lines 122–129."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("genuinely-entangled"), DeclarationHandle.Create(Module + ".genuinelyEntangled"),
                H("Entanglement of every nonzero fixed vector"), StatementSource.FromAuthor(Disp(EntanglementDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Every nonzero vector of the common fixed subspace must fail to factor across every "
                    + "bipartition whose two sides are nonempty. This condition itself does not assert "
                    + "that the fixed subspace contains a nonzero vector. See final_5.tex, lines 120–136 and 141."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("commutation-space"), DeclarationHandle.Create(Module + ".commutationSpace"),
                H("The span of the commutation vectors"), StatementSource.FromAuthor(Disp(SpaceDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For prime p, take the ZMod p linear span of the commutation vectors of all ordered "
                    + "pairs of generators. The pair ij runs through Fin k times Fin k. "
                    + "This is the space K of final_5.tex, lines 375–391."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("generated-operators"), DeclarationHandle.Create(Module + ".generatedOperators"),
                H("Finite products of the generator matrices"), StatementSource.FromAuthor(Disp(GeneratedDefinition)),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The generated submonoid is the smallest multiplicatively closed collection containing "
                    + "the identity and all generator matrices. Its elements are finite products of those "
                    + "matrices. This formulation does not require a group structure on PauliWord."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("is-stabilizer"), DeclarationHandle.Create(Module + ".IsStabilizer"),
                H("Commutativity and exclusion of nonidentity scalars"), StatementSource.FromAuthor(Disp(StabilizerDefinition)),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The generator matrices commute pairwise, and every scalar matrix in their generated "
                    + "submonoid has scalar equal to one. The identity is already in that submonoid. "
                    + "For nonzero p the Pauli matrices form a finite collection of invertible matrices, "
                    + "so the generated submonoid is a group. These are the two stabilizer conditions "
                    + "of final_5.tex, lines 218–223."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Module + ".claim"),
                H("The commutation-rank bound"),
                StatementSource.FromAuthor(Disp(EqF(Named("claim"), Parenthesized(ClaimStatement)))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every positive number N of parties, every prime p and every family G of k Pauli "
                    + "words generating a stabilizer, genuine entanglement implies the displayed rank bound. "
                    + "This is Conjecture 1 in final_5.tex, lines 457–463. Subtraction and Nat.div are "
                    + "natural-number operations: because p is prime, the quotient is exactly the ceiling "
                    + "of (N minus one) divided by (p minus one). The proof hp supplies the nonzero modulus "
                    + "and the instance ⟨hp⟩ in the explicitly applied commutationSpace. CoeSort.coe displays "
                    + "the submodule as its type of elements; its finrank is a natural number."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Module + ".result"),
                H("Genuine entanglement forces the rank bound"), StatementSource.FromAuthor(Disp(ClaimStatement)),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Products of tensor-product matrices are computed coordinate by coordinate, and "
                        + "multiplication of the root-of-unity phases follows addition in ZMod p. A word "
                        + "with zero x and z is a scalar matrix. Multiplying two words again gives a word: "
                        + "add x and z, and add both phases and the sum of a.z(n)b.x(n). There are "
                        + "finitely many words when p is nonzero, and every word matrix is invertible, "
                        + "since the shift and clock matrices and the scalar phase are invertible.")),
                    Paragraph(Text(
                        "A commuting family of complex endomorphisms on a nonzero finite-dimensional "
                        + "space has a common eigenvector: its Lie span is abelian, and a nontrivial weight "
                        + "space supplies the vector. Now consider matrices c(i) times A(i) tensor B(i), "
                        + "with the B(i) commuting, and let W be their common fixed subspace. The actions "
                        + "of identity tensor B(i) preserve W and commute there. A nonzero W therefore "
                        + "contains a common eigenvector w with eigenvalues χ(i). Choose a nonzero "
                        + "coordinate w(xy), and take a(x) = w(x,xy.2) and b(y) = w(xy.1,y). The eigenvector "
                        + "equations give B(i)b = χ(i)b, and the fixed-vector equations give "
                        + "(c(i)χ(i))A(i)a = a. Hence a tensor b is fixed by every c(i)A(i) tensor B(i), "
                        + "and its coordinate at xy is w(xy) squared, so it is nonzero.")),
                    Paragraph(Text(
                        "The local displacement identity gives the commutation phase "
                        + "a.z(n)b.x(n) minus a.x(n)b.z(n). Multiplying over the parties shows that the "
                        + "global commutation phase is the root of unity raised to the representative "
                        + "of the sum of these coordinates. A word with some nonzero x or z coordinate "
                        + "has trace zero: its trace is its scalar phase times the product of the local "
                        + "displacement traces, and the corresponding local trace vanishes.")),
                    Paragraph(Text(
                        "Let S be a finite set of words and T its generated matrix submonoid, excluding "
                        + "nonidentity scalar matrices. The word matrices form a finite submonoid "
                        + "containing T, so T is finite. Every element of T other than the identity "
                        + "has trace zero: if all its x and z coordinates vanished it would be scalar and "
                        + "therefore the identity. Thus M, the sum of all matrices in T, has trace equal "
                        + "to Fintype.card(Fin N → ZMod p) cast from ℕ to ℂ. This cast is nonzero, so M "
                        + "is nonzero and Mv is nonzero for some vector v. Left multiplication by any "
                        + "generator is injective on the finite set T, since the generator is invertible; "
                        + "it therefore permutes T. Consequently every generator fixes Mv.")),
                    Paragraph(Text(
                        "Suppose the sums of the commutation coordinates over a set Q vanish for every "
                        + "pair in S, and take a nonzero common fixed vector ψ. Applying the global "
                        + "commutation identity to ψ forces the total phase sum to be zero, by "
                        + "primitivity of windowRoot(p). The complementary sum is therefore zero too. "
                        + "Split configurations into their restrictions to Q and its complement using "
                        + "the corresponding equivalence of function spaces. Each word matrix becomes "
                        + "c(i)A(i) tensor B(i), and the complementary matrices B(i) commute by the "
                        + "vanishing complementary phase sums. Transport ψ through this equivalence "
                        + "and apply the preceding product-vector construction. Transporting back gives "
                        + "a nonzero common fixed vector factoring across Q.")),
                    Paragraph(Text(
                        "For a family u of r vectors with m coordinates over ZMod p, assume "
                        + "r(p minus one) is less than m. Define f(i) as the sum over j of "
                        + "u(i,j) times X(j) to the power (p minus one). The sum of their total degrees is at most "
                        + "r(p minus one), hence is less than m. Chevalley–Warning makes the number of "
                        + "common zeros divisible by p. Zero is one common zero, so it cannot be the only "
                        + "one. Choose a nonzero common zero x. Fermat's identity makes x(j) to the power "
                        + "p minus one equal to one on its nonempty support Q and zero elsewhere. "
                        + "Therefore the sum of u(i,j) over Q is zero for every i.")),
                    Paragraph(Text(
                        "Apply this fact to the first n coordinates of a basis b of a submodule K in "
                        + "ZMod p to the power n plus one. If n exceeds finrank(K)(p minus one), it "
                        + "produces a nonempty Q in Fin n whose coordinate-sum linear map L vanishes "
                        + "on every basis vector. Thus L is zero on K. Consequently, whenever every "
                        + "nonempty Q has some vector of K with nonzero coordinate sum, n is at most "
                        + "finrank(K)(p minus one).")),
                    Paragraph(Text(
                        "For the generators G on n plus one parties, put S equal to their finite image. "
                        + "Its generated submonoid lies in generatedOperators(G), so scalar exclusion "
                        + "gives the nonzero common fixed vector just constructed. If a nonempty Q in "
                        + "Fin n had zero coordinate sum for every vector of commutationSpace(G), "
                        + "the generator-pair commutation vectors would have zero sum there. Embed Q "
                        + "into Fin(n plus one) by castSucc and call its image R. The set R is nonempty "
                        + "and its complement contains the last party. The product-vector construction "
                        + "then gives a nonzero vector in stabilizerSubspace(G) factoring across R, "
                        + "contrary to genuine entanglement. Thus every such Q has a vector with nonzero "
                        + "sum, and the rank estimate applies to commutationSpace(G).")),
                    Paragraph(Text(
                        "Finally, write the positive N as n plus one and use p minus one greater than "
                        + "zero. The inequality n ≤ (p minus one)finrank(commutationSpace(G)), after "
                        + "adding p minus two on both sides, gives the displayed bound by the "
                        + "natural-number division criterion. This includes N equal to one."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("makuta-kuzaka-augusiak-2023-stabilizer-commutation-rank"),
                    ResolutionKind.Proved)))));
}
