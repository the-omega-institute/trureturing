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
                "For support of size two or three, write a(i) = norm(u(i)), m(i) = weight(u,i), and S = sum a(i)/m(i). The off-diagonal entries are minus v(i) conjugate(u(j)), so each m(i) norm(v(i)) is bounded by coherence. Normalization gives 1 <= sum a(i) norm(v(i)) <= coherence times S, proving the lower bound S inverse. The displayed optimalParameter is normalized and attains that bound. If all coordinates are nonzero, the sum of the gaps between each weighted bound and the real part of conjugate(u(i))v(i) is zero. Each gap is nonnegative, so every gap vanishes. Equality of real part and norm forces a nonnegative real phase, and cancellation of each nonzero conjugate(u(i)) fixes v(i). Injectivity of multiplication by F* then fixes G. If the support is the singleton r, take v(r) = inverse(conjugate(u(r))) and every other coordinate zero. Its cross-Gram is diagonal with entry zero at r and one elsewhere, hence its coherence is zero. A nonzero u excludes empty support. No converse claiming that full support is necessary for uniqueness is asserted.", true))));

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
