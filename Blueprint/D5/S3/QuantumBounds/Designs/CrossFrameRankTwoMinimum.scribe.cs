using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds.Designs;

internal sealed class CrossFrameRankTwoMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/Designs/CrossFrameRankTwoMinimum.";
    private static readonly LibraryNoteRef Background = LibraryNoteRef.Create("D5/L/QuantumBounds/aceska2022crossframe");
    private static Formula K => F.Id("K");
    private static Formula U => F.Id("u");
    private static Formula V => F.Id("v");
    private static Formula Frame => F.Id("F");
    private static Formula G => F.Id("G");
    private static Formula C => F.Id("C");
    private static Formula I => F.Id("i");
    private static Formula J => F.Id("j");
    private static Formula FinThree => Call("Fin", D(3));
    private static Formula Vector => Seq(FinThree, Sp, To, Sp, K);
    private static Formula Mat(byte rows) => Call("Matrix", Call("Fin", D(rows)), FinThree, K);
    private static Formula T => Call("inv", Call("total", U));
    private static Formula Mu(Formula g) => Call("coherence", Call("crossGram", Frame, g));
    private static Formula Card => Call("card", Call("support", U));
    private static Formula Adj(Formula x) => Call("conjTranspose", x);
    private static Formula Gram(Formula v) => Call("gram", U, v);
    private static Formula Reconstruction(Formula v) => Call("reconstruct", Frame, Gram(v));
    private static Formula Normalized(Formula v) => Eq(Call("dotProduct", Call("star", U), v), D(1));
    private static Formula Spans(Formula f) => Eq(Call("span", K, Call("range", Call("col", f))), Call("top"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rank-two frame with three columns has an explicit dual attaining the exact smallest off-diagonal cross-Gram magnitude. Full support of its null vector forces uniqueness over either scalar field.",
        H("Exact dual coherence for a rank-two three-column frame"),
        Blocks(
            Paragraph(Text("The cross-Gram convention is C = F*G, with C(i,j) = sum over r of conjugate(F(r,i)) G(r,j). Duality means FG* = I. Taking adjoints gives GF* = I. Thus both column families span the two-dimensional space. With Mathlib's convention, reconstruction uses the coefficient inner(G(i),x), which is linear in x. The frame and coherence terminology is that of Aceska and Kaczanowski; the exact minimization and uniqueness statements below are separate mathematical deductions.")),
            Node("Dual", "Actual dual matrices", Scalar(All("F", Mat(2), All("G", Mat(2), Iff(Call("Dual", Frame, G), Eq(Mul(Frame, Adj(G)), D(1)))))),
                "The identity includes every entry of the two by two product. No symmetry, canonicality or unit-norm condition is imposed."),
            Node("crossGram", "Cross-Gram orientation", Scalar(All("F", Mat(2), All("G", Mat(2), Eq(Call("crossGram", Frame, G), Mul(Adj(Frame), G))))),
                "The first family is conjugated. The matrix has three rows and three columns."),
            Node("coherence", "Six ordered off-diagonal entries", Scalar(All("C", Mat(3), Eq(Call("coherence", C), Seq(new Formula.Subscript(Max, Seq(I, Comma, Sp, J, Colon, Sp, FinThree, Comma, Sp, Ne(I,J))), Sp, new Formula.Norm(Call("entry", C,I,J)))))),
                "The finite maximum uses nonnegative norms and is then coerced to the reals. All six ordered off-diagonal entries participate; no diagonal entry or assumed Hermitian symmetry is used."),
            Node("support", "Null-vector support", Scalar(All("u", Vector, Eq(Call("support", U),
                Seq(OpenBrace, I, Colon, Sp, FinThree, Sp, Mid, Sp,
                    Ne(Call("apply", U, I), D(0)), CloseBrace)))),
                "This is the finite set of indices i with u(i) different from zero."),
            Node("weight", "Magnitudes away from one coordinate", Scalar(All("u", Vector, All("i", FinThree, Eq(Call("weight", U,I), Seq(new Formula.Subscript(Max, Seq(J, Colon, Sp, FinThree, Comma, Sp, Ne(J,I))), Sp, new Formula.Norm(Call("apply", U,J))))))),
                "The weight m(i) is the largest magnitude of the other two coordinates. At least two nonzero coordinates make every weight positive."),
            Node("total", "The reciprocal denominator", Scalar(All("u", Vector, Eq(Call("total", U), Sum(new Formula.Fraction(new Formula.Norm(Call("apply", U,I)), Call("weight",U,I)))))),
                "A zero numerator contributes zero when at least two coordinates are nonzero. The singleton case is treated separately rather than using division by zero as a minimization argument."),
            Node("gram", "The rank-one correction", Scalar(All("u", Vector, All("v", Vector, Eq(Gram(V), Sub(D(1), Call("vecMulVec", V,Call("star",U))))))),
                "For a normalized parameter v, the cross-Gram matrix is I minus v u*. It is an oblique projection, without a self-adjointness requirement."),
            Node("reconstruct", "Explicit actual-dual reconstruction", Scalar(All("F", Mat(2), All("C", Mat(3), Eq(Call("reconstruct",Frame,C), Mul(Mul(Call("inv",Mul(Frame,Adj(Frame))),Frame),C))))),
                "Rank two makes FF* nonsingular. The inverse here is the ordinary matrix inverse on that hypothesis."),
            Node("optimalParameter", "An optimizer with the zero convention", Scalar(All("u", Vector, All("i", FinThree,
                Eq(Call("apply",Call("optimalParameter",U),I), Call("ite",Eq(Call("apply",U,I),D(0)),D(0),
                    Mul(Call("ofReal",new Formula.Fraction(T,Call("weight",U,I))),
                        new Formula.Fraction(Call("apply",U,I),Call("ofReal",new Formula.Norm(Call("apply",U,I)))))))))),
                "For a nonzero coordinate, v(i) = (T/m(i)) u(i)/norm(u(i)), where T is the inverse of total(u). Real factors are embedded in K. For a zero coordinate, v(i) is zero."),
            Node("dual_parameterization", "All duals and the converse construction", Parameterization(),
                "The kernel of F is the span of any nonzero null vector u, by rank-nullity. For a dual, every column of I minus G*F lies in this kernel. Taking adjoints gives C = I minus v u*, and u*C = 0 gives u*v = 1. Conversely, a normalized v yields the displayed reconstructed matrix, whose cross-Gram is C and whose two reconstruction identities hold. Multiplication by F* is injective, so the cross-Gram determines the actual dual.", true),
            Node("rank_two_minimum", "Attainment and full-support uniqueness", Minimum(),
                "For support of size two or three, write a(i) = norm(u(i)), m(i) = weight(u,i), and S = sum a(i)/m(i). The off-diagonal entries are minus v(i) conjugate(u(j)), so each m(i) norm(v(i)) is bounded by coherence. Normalization gives 1 <= sum a(i) norm(v(i)) <= coherence times S, proving the lower bound S inverse. The displayed optimalParameter is normalized and attains that bound. If all coordinates are nonzero, the sum of the gaps between each weighted bound and the real part of conjugate(u(i))v(i) is zero. Each gap is nonnegative, so every gap vanishes. Equality of real part and norm forces a nonnegative real phase, and cancellation of each nonzero conjugate(u(i)) fixes v(i). Injectivity of multiplication by F* then fixes G. If the support is the singleton r, take v(r) = inverse(conjugate(u(r))) and every other coordinate zero. Its cross-Gram is diagonal with entry zero at r and one elsewhere, hence its coherence is zero. A nonzero u excludes empty support. No converse claiming that full support is necessary for uniqueness is asserted.", true),
            UnitColumnApplication())));

    private static DocumentBlock UnitColumnApplication()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), s = F.Id("s"), total = F.Id("S");
        Formula oneThird = new Formula.Fraction(D(1), D(3));
        Formula twoThirds = new Formula.Fraction(D(2), D(3));
        Formula threeHalves = new Formula.Fraction(D(3), D(2));
        Formula transpose(Formula x) => Call("transpose", x);
        Formula identity(byte size) => Call("identity", D(size));
        Formula tight = Eq(Mul(Frame, transpose(Frame)), Mul(threeHalves, identity(2)));
        return new DocumentBlock.Section(H("Application: real Euclidean unit columns and the full equality case"), Blocks(
            Paragraph(Text("Let F be any real 2 by 3 matrix of rank two, with columns f(1), f(2), f(3) satisfying sum over r = 1,2 of F(r,i)^2 = 1 for each i. These are Euclidean unit columns in the real plane: in Lean this means EuclideanSpace R (Fin 2), or the explicit sum-of-squares condition, rather than the default supremum norm on raw Fin 2 functions. Let G range over every real 2 by 3 matrix satisfying FGᵀ = I(2). Write mu(F,G) for the maximum of |(FᵀG)(i,j)| over all six ordered pairs i different from j. No norm, symmetry, equal-diagonal, sign or canonicality hypothesis is imposed on G. Transposition gives GFᵀ = I(2), so these are actual dual frames with both reconstruction identities.")),
            Paragraph(Text("For every such F and every such actual dual G, the application gives the sharp bound and the following complete equality characterization:")),
            new DocumentBlock.DisplayFormula(Le(oneThird, Mu(G))),
            new DocumentBlock.DisplayFormula(Iff(Eq(Mu(G), oneThird), And(tight, Eq(G, Mul(twoThirds, Frame))))),
            Paragraph(Text("The argument applies the existing frozen "), Ref(Prefix + "rank_two_minimum"), Text(" and "), Ref(Prefix + "dual_parameterization"), Text(" to K = R. Their source is CrossFrameRankTwoMinimum.lean at revision 7767e9e94e8aece1b1661dc4a9ddad628ad3f55e, source blob dab79b802b7e45d4339fb65ff9b8b966353fc28f, with mathlib pinned to 56a005855ea17e0b0958f73ec801ae140b0a1679. The frozen result supplies exact optimization, actual attainment and full-support uniqueness. The unit-column geometry and equality classification are derived below as a source-level application; they are not a separately declared Lean theorem in this module.")),
            Paragraph(Text("Choose a nonzero real null vector u by rank-nullity; the kernel has dimension one. Singleton support would give u(i) f(i) = 0 for a nonzero u(i), contradicting the unit column condition. Thus support has size two or three. Put w(i) = max over j different from i of |u(j)| and S = sum over i of |u(i)|/w(i), exactly weight and total above. Every w(i) and S are positive. Rescaling u by a nonzero scalar multiplies every magnitude and weight by the same positive factor; S is unchanged. Coordinate signs and a simultaneous relabelling of columns and null coordinates also leave S unchanged. Specializing rank_two_minimum now supplies an actual dual H attaining coherence 1/S and proves mu(F,G) >= 1/S for every actual G. This is a minimum over reconstructed matrices, not merely an infimum over abstract cross-Gram parameters.")),
            Paragraph(Text("If support has size two, say at i and j, then u(i) f(i) = -u(j) f(j). Taking Euclidean norms gives |u(i)| = |u(j)| = t > 0. All three weights equal t, including the weight at the zero coordinate. Hence S = 2 and the attained minimum is exactly 1/2. Conversely, a collinear pair of unit columns gives such a relation; rank two places the remaining column off that line, and nullity one fixes the same support for every nonzero null vector. No uniqueness assertion from the full-support clause is used in this case.")),
            Paragraph(Text("For full support, relabel the magnitudes as 0 < a <= b <= c and set x(i) = sign(u(i)) f(i). The x(i) are real Euclidean unit vectors and a x(1) + b x(2) + c x(3) = 0. Thus c = norm(a x(1) + b x(2)) <= a+b. Equality c = a+b would give (a+b)^2 = a^2+b^2+2ab inner(x(1),x(2)), so inner(x(1),x(2)) = 1. Then norm(x(1)-x(2))^2 = 2-2 = 0, and x(1) = x(2). The dependence forces x(3) = -x(1). Undoing the signs and relabelling makes all columns collinear, contrary to rank two. Consequently c < a+b.")),
            Paragraph(Text("The excluded-coordinate maxima are (c,c,b), also when magnitudes tie. Therefore the exact denominator and rational identity are:")),
            new DocumentBlock.DisplayFormula(Eq(total, Add(new Formula.Fraction(Add(a,b),c), new Formula.Fraction(c,b)))),
            new DocumentBlock.DisplayFormula(Eq(Sub(D(3),total), Add(
                new Formula.Fraction(Sub(b,a),b),
                new Formula.Fraction(Mul(Sub(c,b),Sub(Add(a,b),c)),Mul(b,c))))),
            Paragraph(Text("Both summands in 3-S are nonnegative. Their sum vanishes only if b = a and then c = b, since a+b-c > 0; conversely a = b = c gives S = 3. Together with support two, this proves 0 < S <= 3, with S = 3 exactly when all three magnitudes |u(i)| are equal and positive. The strict triangle is essential: the excluded scalar boundary a = b, c = a+b would also give S = 3. For every actual dual, mu(F,G) >= 1/S >= 1/3. In full support with unequal magnitudes the attained minimum is strictly greater than 1/3; in full support the minimizing actual dual is unique by the frozen result.")),
            Paragraph(Text("Suppose now an actual G has mu(F,G) = 1/3. The preceding inequalities force S = 3. Write u = t s with t > 0 and each s(i) equal to +1 or -1, so Fs = 0. The unit vectors h(i) = s(i) f(i) sum to zero. For distinct i,j and the remaining index k, h(i)+h(j) = -h(k); squaring gives inner(h(i),h(j)) = -1/2. Hence the signed equilateral Gram identity is:")),
            new DocumentBlock.DisplayFormula(Eq(Mul(transpose(Frame),Frame), Sub(
                Mul(threeHalves,identity(3)), Mul(new Formula.Fraction(D(1),D(2)),Call("vecMulVec",s,s))))),
            Paragraph(Text("Multiplying on the left by F and using Fs = 0 yields (FFᵀ)F = (3/2)F. Rank two makes F surjective onto the real plane, so FFᵀ = (3/2)I(2). Thus C = (2/3)F is an actual dual and is the canonical dual (FFᵀ)⁻¹F. Its cross-Gram is:")),
            new DocumentBlock.DisplayFormula(Eq(Mul(transpose(Frame),Mul(twoThirds,Frame)), Sub(
                identity(3),Mul(oneThird,Call("vecMulVec",s,s))))),
            Paragraph(Text("Every one of its six ordered off-diagonal entries has absolute value 1/3. To identify the given actual matrix G, take the minimizing actual H supplied above. Both C and G have coherence equal to that of H. All coordinates of u are nonzero, so the actual-matrix uniqueness clause of rank_two_minimum gives C = H and G = H. Therefore G = (2/3)F. Uniqueness of a cross-Gram parameter alone is not being substituted for uniqueness of the dual matrix.")),
            Paragraph(Text("Conversely, assume FFᵀ = (3/2)I(2). Then P = (2/3)FᵀF is symmetric, acts as the identity on the two-dimensional range of Fᵀ, and vanishes on ker(F). Indeed P(Fᵀy) = Fᵀy and Pv = 0 whenever Fv = 0. The orthogonal decomposition of the real three-dimensional space as range(Fᵀ) plus ker(F) therefore gives P = I(3)-vvᵀ for a Euclidean unit vector v spanning ker(F). On the diagonal, unit column norms give P(i,i) = 2/3, hence v(i)^2 = 1/3 for every i. Set s = sqrt(3) v. Then s(i) is +1 or -1 and Fs = 0. The signed equilateral calculation above applies again. If G = (2/3)F, it is an actual dual and its cross-Gram is I(3)-(1/3)ssᵀ, so its coherence is exactly 1/3. This proves the other direction of the displayed equivalence. It also shows that tightness, a null vector of equal positive coordinate magnitudes, and a signed equilateral triple are equivalent within this domain. In the tight case the minimizing actual dual is uniquely (2/3)F.")),
            Paragraph(Text("Sharpness is realized exactly by the matrix with rows (1,-1/2,-1/2) and (0,sqrt(3)/2,-sqrt(3)/2). Each squared column norm is 1, the determinant of its first two columns is sqrt(3)/2 and is nonzero, its frame operator is (3/2)I(2), and F(1,1,1)ᵀ = 0. With G = (2/3)F, FGᵀ = I(2) and FᵀG has diagonal entries 2/3 and all six off-diagonal entries -1/3. This is an exact equality pair.")),
            Paragraph(Text("Aceska and Kaczanowski's Cross-Frame Potential supplies the frame, dual and coherence terminology and the equilateral tight-frame illustration in Example 5; see "), Ref("D5/L/QuantumBounds/aceska2022crossframe"), Text(". Their Lemma 33 assumes equal diagonal pairings, which are not assumed for arbitrary G here. This application concerns every real Euclidean unit-column rank-two 2 by 3 frame and all its actual duals. The real inner-product and sign argument does not establish an equality classification for arbitrary complex frames. It neither settles the paper's unrestricted Conjecture 41, already refuted in the separate non-unit example, nor claims priority, a new named conjecture settlement, or any conclusion for the wider 2 by 4 and 3 by 5 residuals."))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, bool theorem = false) =>
        Describe.Lean(DescribeId.Create("cross-frame-rank-two-" + name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Background), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    private static Formula Call(string name, params Formula[] args) => args.Length == 0
        ? Seq(Operatorname, Sp, Grp(F.Id(name))) : new Formula.Apply(Seq(Operatorname,Sp,Grp(F.Id(name))),[..args]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),type,body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(name),type,body);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a, Formula b) => Rel(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Le(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Iff,Par(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Sum(Formula x) => Seq(new Formula.Subscript(F.Sum,Seq(I,Colon,Sp,FinThree)),Sp,x);
    private static Formula Scalar(Formula body) => All("K",Call("Type"),Seq(OpenBracket,Call("RCLike",K),CloseBracket,Sp,body));
    private static Formula Hypotheses(Formula body) => Scalar(All("F",Mat(2),Imp(Eq(Call("rank",Frame),D(2)),
        All("u",Vector,Imp(Ne(U,D(0)),Imp(Eq(Call("mulVec",Frame,U),D(0)),body))))));
    private static Formula Parameterization() => Hypotheses(All("G",Mat(2),
        Iff(Call("Dual",Frame,G),Ex("v",Vector,And(Normalized(V),
            And(Eq(Call("crossGram",Frame,G),Gram(V)),Eq(G,Reconstruction(V))))))));
    private static Formula Minimum()
    {
        Formula multi = Imp(Le(D(2),Card),And(All("i",FinThree,Lt(D(0),Call("weight",U,I))),
            And(Lt(D(0),Call("total",U)),And(Eq(G,Reconstruction(Call("optimalParameter",U))),Eq(Mu(G),T)))));
        Formula minimum = All("H",Mat(2),Imp(Call("Dual",Frame,F.Id("H")),Le(Mu(G),Mu(F.Id("H")))));
        Formula unique = Imp(All("i",FinThree,Ne(Call("apply",U,I),D(0))),
            All("H",Mat(2),Imp(Call("Dual",Frame,F.Id("H")),Imp(Le(Mu(F.Id("H")),Mu(G)),Eq(F.Id("H"),G)))));
        return Hypotheses(Ex("G",Mat(2),And(Call("Dual",Frame,G),And(Spans(Frame),And(Spans(G),
            And(Imp(Eq(Card,D(1)),Eq(Mu(G),D(0))),And(multi,And(minimum,unique))))))));
    }
}
