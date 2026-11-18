using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class RectangularBlockPartitionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/RectangularBlockPartition";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rectangle partition with matched sides gives a unitary with an exact tensor factor count.",
        H("Paired partial permutations on rectangle partitions"),
        Blocks(
            Paragraph(Text(
                "Let X, Y and T be arbitrary finite types. Empty types and empty blocks are allowed. " +
                "For each t in T choose finite subsets I(t) of X and J(t) of Y and a bijection " +
                "φ(t): J(t) ≃ I(t). Assume every pair (x,y) belongs to exactly one rectangle " +
                "I(t) × J(t). Here subsets in the bijection are subtype carriers. Equality on " +
                "X and Y is decidable, as it can always be made for finite types.")),
            Paragraph(Text(
                "Define A(t)(i,j) to be 1 if some y in J(t) satisfies y=j and φ(t)(y)=i, and 0 " +
                "otherwise. Put U=∑t A(t)⊗A(t)ᴴ. Its rows are indexed by X×Y and its columns " +
                "by Y×X: the first local factor maps Y to X, and the second maps X to Y. " +
                "Define realignment by R(U)((i,j),(k,l))=U((i,k),(j,l)), with i,l in X and " +
                "j,k in Y. Let Tplus={t in T: J(t) is nonempty}.")),
            Describe.Lean(
                DescribeId.Create("unitary-exact-width"),
                DeclarationHandle.Create(Owner + ".unitary_exact_width"),
                H("Unitarity and exact achieved width"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every such finite X,Y,T,I,J,φ and unique-coverage hypothesis, " +
                        "both Gram identities hold on the original carriers: UᴴU is the identity " +
                        "on Y×X and UUᴴ is the identity on X×Y. The rank of R(U) equals the " +
                        "cardinality of Tplus. Deleting empty blocks gives the displayed exact " +
                        "decomposition of U indexed by Tplus. There are actual row and column " +
                        "maps from Tplus whose submatrix of R(U) is the identity. Finally, for " +
                        "every finite type Q and arbitrary complex factors M(q): Matrix X Y " +
                        "and N(q): Matrix Y X, the equality U=∑q M(q)⊗N(q) implies " +
                        "|Tplus|≤|Q|. No independence or positivity of these factors is assumed.")),
                    Paragraph(Text(
                        "The disjoint union of the rectangles is bijective to X×Y: coverage " +
                        "gives surjectivity and uniqueness gives injectivity. Given an input " +
                        "(j,l), its rectangle contains (l,j). Inside that rectangle route it " +
                        "to (φ(t)(j),φ(t)⁻¹(l)). Both entries stay in the same rectangle. The " +
                        "inverse sends (i,k) to (φ(t)⁻¹(i),φ(t)(k)) using the rectangle of (i,k). " +
                        "The tensor sum is exactly the coordinate matrix of this equivalence. " +
                        "Applying SequentialRegisterCircuit.coordinate_gram to the route and " +
                        "its inverse gives the two Gram identities.")),
                    Paragraph(Text(
                        "For each nonempty block t choose j(t) in J(t) and put i(t)=φ(t)(j(t)). " +
                        "Rectangle disjointness gives A(u)(i(t),j(t))=1 exactly when u=t. " +
                        "Consequently R(U) restricted to rows (i(s),j(s)) and columns " +
                        "(j(t),i(t)) is the identity on Tplus. The existing rank_submatrix_le " +
                        "and rank_one results give the lower rank bound. This construction is " +
                        "also valid for empty Tplus, with empty row and column families.")),
                    Paragraph(Text(
                        "For arbitrary factors, realignment of ∑q M(q)⊗N(q) is B C, where " +
                        "B((i,j),q)=M(q)(i,j) and C(q,(k,l))=N(q)(k,l). Thus " +
                        "rank(R(U))≤rank(B)≤|Q| by rank_mul_le_left and rank_le_card_width. " +
                        "This uses ordinary vectorization of N, with no conjugation. Apply it " +
                        "first to the decomposition after deleting empty blocks for the upper " +
                        "rank bound, and then to any proposed decomposition for the arbitrary " +
                        "factor lower bound. If J(t) is empty, A(t)=0; the bijection also makes " +
                        "I(t) empty. If X or Y is empty, every block is empty.")),
                    Paragraph(Text(
                        "The supplied decomposition achieves width |Tplus| and the lower bound " +
                        "rules out fewer terms for this same operator U with these original " +
                        "local carriers. This is exact generalized operator Schmidt rank in " +
                        "the sense of allowing different input and output local spaces. It " +
                        "makes no minimum-width assertion across other operators of the same " +
                        "dimensions. No physical swap is postcomposed.")),
                    Paragraph(Text(
                        "Realignment rank as a tensor factor count is established mathematics: " +
                        "Müller-Hermes and Nechita, arXiv:1612.07616v1, Proposition 2.1 and " +
                        "Remark 2.2, discuss the rank bridge; Definition 3.1 and Lemma 3.2 " +
                        "give permutation-tableaux constructions with preserved local spaces. " +
                        "Tyson, arXiv:quant-ph/0306144v2, Definition 1, permits four distinct " +
                        "local input and output spaces. The construction here proves the " +
                        "general rectangle-partition route and its identity-minor certificate " +
                        "on the exchanged rectangular carriers. No global novelty claim is made."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Card(Formula a) => Call("card", a);
    private static Formula Mat(Formula a, Formula b) => Call("Matrix", a, b, V("Complex"));
    private static Formula Prod(Formula a, Formula b) => Call("Prod", a, b);
    private static Formula Sum(string t, Formula type, Formula term) =>
        Seq(new Formula.Subscript(F.Sum, Seq(V(t), Colon, type)), Sp, term);
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Statement()
    {
        Formula X = V("X"), Y = V("Y"), T = V("T"), I = V("I"), J = V("J");
        Formula U = V("U"), P = V("Tplus");
        Formula A = V("A"), t = V("t"), q = V("q");
        Formula M = V("M"), N = V("N"), Q = V("Q"), RU = Call("R", U);
        Formula upper = Eq(U, Sum("t", P,
            Call("kronecker", At(A, Call("val", t)), Call("conjTranspose", At(A, Call("val", t))))));
        Formula minor = Some("rows", new Formula.TypeArrow(P, Prod(X,Y)),
            Some("cols", new Formula.TypeArrow(P, Prod(Y,X)),
                Eq(Call("submatrix", RU, V("rows"), V("cols")), D(1))));
        Formula lower = All("Q", V("FiniteType"),
            All("M", new Formula.TypeArrow(Q, Mat(X,Y)),
                All("N", new Formula.TypeArrow(Q, Mat(Y,X)),
                    Implies(Eq(U, Sum("q", Q, Call("kronecker", At(M,q), At(N,q)))),
                        Le(Card(P), Card(Q))))));
        Formula result = And(Eq(Mul(Call("conjTranspose", U), U), D(1)),
            And(Eq(Mul(U, Call("conjTranspose", U)), D(1)),
                And(Eq(Call("rank", RU), Card(P)), And(upper, And(minor, lower)))));
        return All("X", V("FiniteType"), All("Y", V("FiniteType"),
            All("T", V("FiniteType"),
                All("I", new Formula.TypeArrow(T, Call("Finset", X)),
                    All("J", new Formula.TypeArrow(T, Call("Finset", Y)),
                        All("phi", Call("BlockBijections", I, J),
                            Implies(Call("UniqueRectangleCoverage", I, J), result)))))));
    }
}
