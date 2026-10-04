using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Combinatorics;

internal sealed class TodaSpecializationUnimodalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Combinatorics/TodaSpecializationUnimodalityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/LieTheory/labelle2025toda");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Labelle's recursively defined Toda specialization has a non-unimodal numerator in type C2 at the positive-root coordinates (2,2).",
        H("Refutation of Labelle's Toda numerator unimodality conjecture"),
        Blocks(
            Node("cartan-datum", "Normalized finite-type Cartan data", DatumFormula(),
                "Section 1 fixes a split semisimple Lie algebra over Q and normalizes short roots to squared length 2. For every finite rank r, CartanDatum(r) encodes its finite-type symmetrizable generalized Cartan data. C and G are integer matrices on Fin(r), and d is a positive-integer function. The generalized Cartan axioms, symmetry and positive definiteness of G, G(i,i)=2d(i), and G(i,j)=d(i)C(i,j) are retained. Every index is connected in the Dynkin graph of nonzero off-diagonal Cartan entries to an index with d=1; this is vacuous at rank zero. The integral quadratic form is even on every integral coordinate vector. The tuple fields C,G,d correspond to cartan,gram,d; the displayed constraints correspond to every proof field.", "CartanDatum", true),
            Node("q-factor", "The displayed q-factor", QFactorFormula(),
                "Definition 1.1 defines (q)_alpha as the product over all simple-root coordinates of the factors 1-q^(d(i)j), with 1<=j<=alpha(i). The displayed nested finite products retain every coordinate at arbitrary finite rank. RatFunc.X is the indeterminate in RatFunc(Q). prod(s,f) multiplies f over s, univ(Fin(r)) is the complete coordinate index set, and range(a)={0,...,a-1}.", "qFactor", true),
            Node("quad", "Half the invariant quadratic form", QuadFormula(),
                "The exponent is literally the integer quotient of the Gram quadratic form (alpha,alpha) by 2. The datum supplies evenness for every integral coordinate vector, so this quotient is the exact integer half. Thus quad takes values in Z, with no conversion to a natural number. Powers of RatFunc.X in J use integer exponentiation. Int.ofNat casts the nonnegative root coordinates to Z. The displayed division by 2 is exact because its numerator is even.", "quad", true),
            Node("j", "Definition 1.1's fermionic recursion", JFormula(),
                "Definition 1.1 defines J_alpha in Q(q) for every nonnegative root-lattice coordinate vector. Equation (2) moves the beta=alpha term to the left for nonzero alpha and divides by 1-q^((alpha,alpha)/2). The displayed ite and finite sum are that recursion, with J(D,0)=1. piFinset forms the finite box of all vectors beta with 0<=beta(i)<=alpha(i) in every coordinate. The summand excludes beta=alpha; alpha-beta is pointwise natural subtraction, equal to the root-lattice difference under these bounds. sum(s,f) adds f over s. Every recursive argument has strictly smaller total coordinate height. The definitions contain no certificate values.", "J", true),
            Node("unimodal", "Weak unimodality", UnimodalFormula(),
                "A polynomial is unimodal when its finite coefficient list a(0),...,a(n), with n=natDegree(p), weakly increases up to a peak m and weakly decreases thereafter. The peak lies between 0 and n; decreasing comparisons stop at i<n. This definition applies to signed coefficients as well as nonnegative coefficients and imposes no comparison with the zero tail beyond the degree.", "Unimodal", false),
            Node("c2", "The C2 datum", C2Formula(),
                "The first simple root is short. The Cartan matrix is [[2,−2],[−1,2]], the Gram matrix is [[2,−2],[−2,4]], and d=(1,2). Every CartanDatum field is satisfied. In particular, its quadratic form is 2(x−y)²+2y², strictly positive off the origin. This is the finite reduced crystallographic type C2, the root datum of the split semisimple Lie algebra sp4 over Q.", "c2", false),
            Node("claim", "Labelle, Conjecture 7.3", ClaimFormula(),
                "Conjecture 7.3 states: The polynomial (q)_alpha^2 J_alpha is unimodal. The encoding quantifies over every finite rank r, every normalized finite-type CartanDatum(r), and every nonnegative coordinate vector alpha:Fin(r)->N. The existential polynomial p has image qFactor(D,alpha)^2 J(D,alpha) under the canonical algebra map Q[X] to RatFunc(Q). Injectivity uniquely identifies p with the source polynomial, so its coefficients cannot be changed by the choice of representation.", "claim", true),
            Node("result", "Refutation in type C2 at (2,2)", Disp(new Formula.Not(Call("claim"))),
                "The recursive J values are verified at all nine pairs 0≤a,b≤2, in increasing height, by clearing nonzero denominators. At (2,2), multiplying J by qFactor² gives 1+q+3q²+2q³+5q⁴+2q⁵+3q⁶+q⁷+q⁸. Injectivity of the polynomial algebra map identifies any p in claim with this polynomial. Its coefficients at degrees 2,3,4 are 3,2,5, a strict valley. A peak at or before degree 2 would require 5≤2 on the decreasing side; a later peak would require 3≤2 on the increasing side. Both are impossible. The type-A results and the general positivity conjecture are outside this refutation.", "result", false, DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("labelle-2025-toda-numerator-unimodality-refutation"), ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(string id, string title, Formula formula, string prose,
        string declaration, bool literature, DescribeRole role = DescribeRole.Definition, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("toda-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => args.Length == 0 ? Named(name) : new Formula.Apply(Named(name), [.. args]);
    private static Formula Qualified(string prefix, string name) => Seq(F.Id(prefix), Dot, F.Id(name));
    private static Formula QualifiedCall(string prefix, string name, params Formula[] args) => Apply(Qualified(prefix, name), args);
    private static Formula Apply(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula All(Formula v, Formula type, Formula body) => Seq(Forall, Sp, v, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula v, Formula type, Formula body) => Seq(Exists, Sp, v, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula LambdaOf(Formula v, Formula type, Formula body) => Seq(Lambda, Sp, v, Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ltq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iffn(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula PairType(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula n) => new Formula.Power(a, n);
    private static Formula NatT => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula RatT => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula IntT => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula PolyT => Call("Polynomial", RatT);
    private static Formula R => F.Id("r");
    private static Formula FinR => Call("Fin", R);
    private static Formula Fin2 => Call("Fin", D(2));
    private static Formula AlphaT => Arrow(FinR, NatT);
    private static Formula DatumT => Call("CartanDatum", R);
    private static Formula MatrixT => Call("Matrix", FinR, FinR, IntT);
    private static Formula Entry(Formula g, Formula i, Formula j) => Apply(g, i, j);
    private static Formula Q => Seq(Named("RatFunc"), Dot, F.Id("X"));
    private static Formula Qf(Formula d, Formula a) => Call("qFactor", d, a);
    private static Formula QuadOf(Formula d, Formula a) => Call("quad", d, a);
    private static Formula SumCoordinates(Formula i, Formula body) =>
        Call("sum", Call("univ", FinR), Parenthesized(LambdaOf(i, FinR, body)));
    private static Formula IntegralForm(Formula g, Formula x)
    {
        Formula i = F.Id("i"), j = F.Id("j");
        return SumCoordinates(i, SumCoordinates(j, Mul(Mul(Apply(x,i),Entry(g,i,j)),Apply(x,j))));
    }

    private static Formula DatumFormula()
    {
        Formula c = F.Id("C"), g = F.Id("G"), d = F.Id("d"), i = F.Id("i"), j = F.Id("j"), x = F.Id("x"), b = Beta, k = F.Id("k");
        Formula Diag = All(i, FinR, Eq(Entry(c,i,i), D(2)));
        Formula Off = All(i, FinR, All(j, FinR, Imp(Ne(i,j), Leq(Entry(c,i,j), D(0)))));
        Formula Zeros = All(i, FinR, All(j, FinR, Iffn(Eq(Entry(c,i,j),D(0)), Eq(Entry(c,j,i),D(0)))));
        Formula Sym = All(i, FinR, All(j, FinR, Eq(Entry(g,i,j),Entry(g,j,i))));
        Formula Pos = All(i, FinR, Ltq(D(0),Apply(d,i)));
        Formula u = F.Id("u"), v = F.Id("v");
        Formula graphRelation = LambdaOf(u, FinR, LambdaOf(v, FinR, Ne(Entry(c,u,v), D(0))));
        Formula reachable = QualifiedCall("SimpleGraph", "Reachable",
            QualifiedCall("SimpleGraph", "fromRel", graphRelation), i, j);
        Formula Norm = All(i, FinR, Some(j, FinR, And(reachable, Eq(Apply(d,j),D(1)))));
        Formula Form = SumCoordinates(i,SumCoordinates(j,Mul(Mul(Apply(x,i),Apply(Call("algebraMap",IntT,RatT),Entry(g,i,j))),Apply(x,j))));
        Formula Finite = All(x,Arrow(FinR,RatT),Imp(Ne(x,D(0)),Ltq(D(0),Form)));
        Formula Diagonal = All(i,FinR,Eq(Entry(g,i,i),Mul(D(2),Apply(Seq(Named("Int"),Dot,Named("ofNat")),Apply(d,i)))));
        Formula Symmetrizes = All(i,FinR,All(j,FinR,Eq(Entry(g,i,j),Mul(Apply(Seq(Named("Int"),Dot,Named("ofNat")),Apply(d,i)),Entry(c,i,j)))));
        Formula Even = All(b,Arrow(FinR,IntT),Some(k,IntT,Eq(IntegralForm(g,b),Add(k,k))));
        Formula Conditions = And(Diag,And(Off,And(Zeros,And(Sym,And(Pos,And(Norm,And(Finite,And(Diagonal,And(Symmetrizes,Even)))))))));
        Formula tuple = Parenthesized(Seq(c,Comma,Sp,g,Comma,Sp,d));
        Formula tupleType = PairType(PairType(MatrixT,MatrixT),Arrow(FinR,NatT));
        Formula subtype = Seq(OpenBrace,tuple,Sp,Colon,Sp,tupleType,Sp,Mid,Sp,Conditions,CloseBrace);
        return Disp(All(R,NatT,Eq(DatumT,subtype)));
    }

    private static Formula QFactorFormula()
    {
        Formula d = F.Id("D"), a = Alpha, i = F.Id("i"), j = F.Id("j");
        Formula factors = Call("prod",Call("range",Apply(a,i)),Parenthesized(LambdaOf(j,NatT,
            Sub(D(1),Pow(Q,Mul(Apply(Call("d",d),i),Add(j,D(1))))))));
        Formula product = Call("prod",Call("univ",FinR),Parenthesized(LambdaOf(i,FinR,factors)));
        return Disp(All(R,NatT,All(d,DatumT,All(a,AlphaT,Eq(Qf(d,a),product)))));
    }

    private static Formula QuadFormula()
    {
        Formula d = F.Id("D"), a = Alpha, i = F.Id("i"), j = F.Id("j"), g = Call("gram",d);
        Formula coord(Formula v) => Apply(Seq(Named("Int"),Dot,Named("ofNat")),Apply(a,v));
        Formula form = SumCoordinates(i,SumCoordinates(j,Mul(Mul(coord(i),coord(j)),Entry(g,i,j))));
        return Disp(All(R,NatT,All(d,DatumT,All(a,AlphaT,Eq(QuadOf(d,a),new Formula.Fraction(form,D(2)))))));
    }

    private static Formula JFormula()
    {
        Formula d = F.Id("D"), a = Alpha, b = Beta, i = F.Id("i");
        Formula conditions = And(All(i,FinR,Leq(Apply(b,i),Apply(a,i))),Ne(b,a));
        Formula term = Mul(new Formula.Fraction(Pow(Q,QuadOf(d,b)),Qf(d,Sub(a,b))),Call("J",d,b));
        Formula box = Call("piFinset",Parenthesized(LambdaOf(i,FinR,Call("range",Add(Apply(a,i),D(1))))));
        Formula sum = Call("sum",box,Parenthesized(LambdaOf(b,AlphaT,Call("ite",conditions,term,D(0)))));
        Formula recursive = Mul(new Formula.Fraction(D(1),Sub(D(1),Pow(Q,QuadOf(d,a)))),sum);
        return Disp(All(R,NatT,All(d,DatumT,All(a,AlphaT,Eq(Call("J",d,a),Call("ite",Eq(a,D(0)),D(1),recursive))))));
    }

    private static Formula UnimodalFormula()
    {
        Formula p = F.Id("p"), m = F.Id("m"), i = F.Id("i"), n = Call("natDegree",p);
        Formula coeff(Formula index) => Call("coeff",p,index);
        Formula increasing = All(i,NatT,Imp(Ltq(i,m),Leq(coeff(i),coeff(Add(i,D(1))))));
        Formula decreasing = All(i,NatT,Imp(And(Leq(m,i),Ltq(i,n)),Leq(coeff(Add(i,D(1))),coeff(i))));
        return Disp(All(p,PolyT,Iffn(Call("Unimodal",p),Some(m,NatT,And(Leq(m,n),And(increasing,decreasing))))));
    }

    private static Formula C2Formula()
    {
        Formula c = Call("c2"), i = F.Id("i"), j = F.Id("j");
        Formula cartan = All(i,Fin2,All(j,Fin2,Eq(Entry(Call("cartan",c),i,j),Call("ite",Eq(i,j),D(2),Call("ite",Eq(i,D(0)),new Formula.Negate(D(2)),new Formula.Negate(D(1)))))));
        Formula gram = All(i,Fin2,All(j,Fin2,Eq(Entry(Call("gram",c),i,j),Call("ite",Ne(i,j),new Formula.Negate(D(2)),Call("ite",Eq(i,D(0)),D(2),D(4))))));
        Formula ds = All(i,Fin2,Eq(Apply(Call("d",c),i),Call("ite",Eq(i,D(0)),D(1),D(2))));
        return Disp(And(cartan,And(gram,ds)));
    }

    private static Formula ClaimFormula()
    {
        Formula d = F.Id("D"), a = Alpha, p = F.Id("p");
        Formula mapped = Apply(Call("algebraMap",PolyT,Call("RatFunc",RatT)),p);
        Formula property = And(Eq(mapped,Mul(Pow(Qf(d,a),D(2)),Call("J",d,a))),Call("Unimodal",p));
        return Disp(Iffn(Call("claim"),All(R,NatT,All(d,DatumT,All(a,AlphaT,Some(p,PolyT,property))))));
    }
}
