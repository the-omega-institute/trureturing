using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class OddSquareGreenMassDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Dynamics/OddSquareGreenMass.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A repeated odd hopping block forces quadratic mass in its inverse bidiagonal block.",
        H("Odd repeated blocks and zero-energy Green mass"),
        Blocks(
            Node("green-entry", "Forward-substitution entries", "greenEntry", EntryFormula(),
                "For an even open path, split the sites into even and odd sublattices. "
                + "After alternating diagonal sign changes, its off-diagonal block has positive diagonal "
                + "t(2i) and negative subdiagonal −t(2i+1). The recurrence E is its positive inverse-entry "
                + "formula, with starting column l and row displacement d. Positive hoppings make every E positive.",
                DescribeRole.Definition),
            Node("lower-block", "The finite bidiagonal block", "lowerBlock", BlockFormula(),
                "L(t,n) is a real matrix on Fin n. Its diagonal is t(2i), its subdiagonal is "
                + "−t(2j+1), and all other entries vanish. The proof verifies its inverse by multiplication; "
                + "no invertibility premise is supplied by the caller.", DescribeRole.Definition),
            Node("inverse-mass", "Quadratic inverse mass in an odd square", "odd_square_inverse_paired_mass",
                MassFormula(),
                "All indices are zero based. In the sums, l ranges over Fin q and d over Fin(q−l). "
                + "Each displayed matrix index denotes the Fin(2q+1) element with that natural value. "
                + "The bounds on l and d prove that every index exists, including the endpoints. "
                + "Only the repeated bonds with i<2q are required; this is a finite repetition assumption. "
                + "Forward substitution gives E(t,l,d+1)E(t,q+l+1,d) "
                + "=1/(t(2l)t(2(l+d+1))). The repeated odd block exchanges numerator and denominator "
                + "factors in the shifted interval. Since both endpoint hoppings are at most one, "
                + "each pair has product at least one and sum at least two. There are q(q+1)/2 pairs. "
                + "The conclusion concerns the actual finite inverse, rather than an assumed Green function. "
                + "It does not assert the Tribonacci all-prefix spectral-gap statement: that application "
                + "also needs the exact word-to-hopping correspondence, aligned repeated windows "
                + "and initial short prefixes. No infinite-volume spectrum, localization, quasimode or "
                + "filling hypothesis enters this theorem.", DescribeRole.Theorem),
            new DocumentBlock.Section(H("Application: a Euclidean estimate for the full inverse"), Blocks(
            Paragraph(Text(
                "Let t be a positive real hopping sequence bounded above by one, and let n,a,q be "
                + "natural numbers with q at least one and a+2q+1 at most n. Assume exactly the "
                + "2q repetitions t(2a+i+2q+1)=t(2a+i), for i<2q. Set G=L(t,n) inverse, acting "
                + "on the Euclidean space R^n, x=(1,...,1) and v=x/sqrt(n). The hypotheses imply n>0. "
                + "The quadratic mass theorem has the following consequence, without a new "
                + "mathematical declaration:")),
            new DocumentBlock.DisplayFormula(FullInverseEstimate()),
            Paragraph(Text(
                "The forward-substitution formula transports each local inverse entry to G by "
                + "adding a to both indices: the defining recursion has the same initial term and "
                + "step after this index translation. Thus both exterior portions of the full path "
                + "remain present. All entries of G are nonnegative. Each of the two triangular "
                + "regions from the mass theorem embeds injectively in the full matrix, so "
                + "q(q+1) is at most twice the sum of all entries of G. The factor two bounds the "
                + "regions separately and needs no disjointness premise. The sum equals the "
                + "Euclidean inner product of x with Gx. Cauchy--Schwarz, norm(x)^2=n and "
                + "Gx=sqrt(n)Gv give that this sum is at most n times norm(Gv), proving the estimate.")),
            Paragraph(Text(
                "For an even-start repeated word window, the parameter correspondence is "
                + "m=2q+1, s=2a and N=2n. This supplies the complete-bidiagonal-inverse "
                + "Euclidean consequence of the mass estimate. The following application supplies "
                + "the parity reordering, sign conjugation and spectral conversion for a general "
                + "finite positive open chain. Identifying the actual Tribonacci hopping sequence, "
                + "assembling its repeated windows under a common index convention and treating "
                + "the short prefixes remain separate obligations. No all-prefix Tribonacci "
                + "spectral rate or entropy law is asserted.")))),
            SpectralApplication())));

    private static DocumentBlock SpectralApplication() => new DocumentBlock.Section(
        H("Application: a spectral residual bound for the finite open chain"), Blocks(
        Paragraph(Text(
            "Let n be a natural number with n at least one, and let t : N -> R be strictly "
            + "positive at every natural index. No upper bound on t is needed for this conversion. "
            + "On the actual sites 0,...,2n-1 define the real symmetric open-chain matrix H by:")),
        new DocumentBlock.DisplayFormula(OpenChainFormula()),
        Paragraph(Text(
            "The diagonal is zero, the last physical bond is t(2n-2), and there is no closing "
            + "bond. In particular, n=1 gives two sites joined only by t(0). Put B=L(t,n), the "
            + "lowerBlock defined above. Its diagonal is t(2i), its subdiagonal in row i is "
            + "-t(2i-1) for 1<=i<n, and all other entries vanish. Since B is lower triangular "
            + "with positive diagonal, its determinant is positive and its ordinary inverse G exists:")),
        new DocumentBlock.DisplayFormula(InvertibleBlockFormula()),
        Paragraph(Text(
            "Reorder the coordinates into even sites followed by odd sites. Write Hpar for the "
            + "matrix in this order and C(i,j)=H(2i,2j+1), for 0<=i,j<n. Then C has diagonal "
            + "t(2i), positive subdiagonal t(2i-1) in row i, and zeros elsewhere. The sign matrix "
            + "D=diag((-1)^i), for 0<=i<n, is orthogonal and satisfies D squared equals I. "
            + "Conjugation preserves the diagonal of C and reverses its subdiagonal, giving:")),
        new DocumentBlock.DisplayFormula(ParityConjugationFormula()),
        Paragraph(Text(
            "Take any Euclidean unit vector v in R^n, and define u in the original site order "
            + "by u(2i)=0 and u(2i+1)=(DGv)(i). Since BG=I, the even part of Hu is CDGv=DBGv=Dv "
            + "and its odd part is zero. Permuting coordinates and changing their signs preserve "
            + "Euclidean norms. Thus:")),
        new DocumentBlock.DisplayFormula(ResidualVectorFormula()),
        Paragraph(Text(
            "Moreover BGv=v and norm(v)=1 imply Gv is nonzero, hence u is nonzero. "
            + "The finite real symmetric matrix H has a real orthonormal eigenbasis e(k) "
            + "with real eigenvalues lambda(k), for 0<=k<2n. Expand u in that basis, with "
            + "real coefficients c(k), and let alpha be the minimum absolute eigenvalue:")),
        new DocumentBlock.DisplayFormula(EigenbasisFormula()),
        Paragraph(Text(
            "The index set is finite and nonempty because 2n>0. Each absolute eigenvalue "
            + "is at least alpha. Parseval applied to u and Hu therefore gives:")),
        new DocumentBlock.DisplayFormula(ParsevalFormula()),
        Paragraph(Text(
            "Choose an index k0 attaining the minimum, put lambda=lambda(k0) and z=e(k0). "
            + "The vector z has norm one and is nonzero. Taking nonnegative square roots in "
            + "the preceding inequality and substituting norm(u)=norm(Gv) proves:")),
        new DocumentBlock.DisplayFormula(SpectralResidualFormula()),
        Paragraph(Text(
            "The selected z is an eigenvector of the actual H. The auxiliary residual vector "
            + "u need not be an eigenvector. This argument applies to every finite positive "
            + "open chain and every Euclidean unit v, without repetition or an upper hopping bound.")),
        Paragraph(Text(
            "Now impose the preceding full-inverse estimate's additional hypotheses: t(i)<=1 "
            + "for every i, q>=1, a+2q+1<=n, and t(2a+i+2q+1)=t(2a+i) for every i<2q. "
            + "Use the same vector v=(1,...,1)/sqrt(n) as in that estimate. It gives "
            + "q(q+1)<=2n norm(Gv), while the spectral argument gives an eigenvalue lambda "
            + "of minimum absolute value with abs(lambda) norm(Gv)<=1. Multiplying the first "
            + "inequality by the nonnegative abs(lambda), then using the second, yields:")),
        new DocumentBlock.DisplayFormula(RepeatedWindowSpectralFormula()),
        Paragraph(Text(
            "Here Spec(H) is the finite real spectrum and delta is its distance from zero; "
            + "division is valid because q>=1. This completes the generic finite positive-path "
            + "conversion from full-inverse mass to a spectral bound. A quantitative rate along "
            + "all actual Tribonacci prefixes still requires the exact word hoppings t(i)=t(W(i)), "
            + "aligned repeated windows and the full-inverse mass estimate under one common "
            + "index convention, together with the initial short prefixes. Entropy scaling "
            + "requires a separate argument about physical states and spatial cuts. Neither an "
            + "all-prefix Tribonacci spectral rate nor a physical entropy law follows from this "
            + "application alone."))));

    private static Formula OpenChainFormula()
    {
        var n=F.Id("n"); var i=F.Id("i"); var j=F.Id("j"); var t=F.Id("t");
        var iv=Call("val",i); var jv=Call("val",j);
        var sites=Call("Fin",Mul(D(2),n));
        return All("i",sites,All("j",sites,Eq(At(F.Id("H"),i,j),
            Call("ite",Eq(Add(iv,D(1)),jv),At(t,iv),
                Call("ite",Eq(Add(jv,D(1)),iv),At(t,jv),D(0))))));
    }

    private static Formula InvertibleBlockFormula()
    {
        var b=F.Id("B"); var g=F.Id("G"); var n=F.Id("n"); var i=F.Id("i");
        var product=Seq(new Formula.Subscript(Prod,Seq(i,Sp,F.Lt,Sp,n)),Sp,
            At(F.Id("t"),Mul(D(2),i)));
        return new Formula.Aligned([
            Eq(b,Call("L",F.Id("t"),n)),
            Seq(Eq(Call("det",b),product),Sp,F.Gt,Sp,D(0)),
            Eq(g,new Formula.Power(b,new Formula.Negate(D(1)))),
            Eq(Mul(b,g),F.Id("I"))]);
    }

    private static Formula ParityConjugationFormula()
    {
        var c=F.Id("C"); var d=F.Id("D"); var b=F.Id("B");
        var block=Seq(Begin,Grp(F.Id("pmatrix")),D(0),Amp,c,RowBreak,
            new Formula.Power(c,F.Id("T")),Amp,D(0),End,Grp(F.Id("pmatrix")));
        return new Formula.Aligned([
            Eq(F.Id("Hpar"),block), Eq(Square(d),F.Id("I")),
            Eq(Mul(Mul(d,c),d),b), Eq(Mul(c,d),Mul(d,b))]);
    }

    private static Formula ResidualVectorFormula()
    {
        var u=F.Id("u"); var v=F.Id("v"); var d=F.Id("D");
        var gv=At(F.Id("G"),v); var hu=At(F.Id("H"),u);
        Formula Part(Formula x,string name) => new Formula.Subscript(x,Seq(Mathrm,Grp(F.Id(name))));
        return new Formula.Aligned([
            Eq(Part(u,"even"),D(0)), Eq(Part(u,"odd"),At(d,gv)),
            Eq(Part(hu,"even"),At(d,v)), Eq(Part(hu,"odd"),D(0)),
            Eq(new Formula.Norm(u),new Formula.Norm(gv)),
            Eq(new Formula.Norm(hu),D(1))]);
    }

    private static Formula EigenbasisFormula()
    {
        var k=F.Id("k"); var n=F.Id("n"); var ek=At(F.Id("e"),k);
        var lk=At(LambdaLower,k); var ck=At(F.Id("c"),k);
        return new Formula.Aligned([
            Eq(At(F.Id("H"),ek),Mul(lk,ek)),
            Eq(F.Id("u"),SumBelow("k",Mul(D(2),n),Mul(ck,ek))),
            Eq(Alpha,Seq(new Formula.Subscript(Min,Seq(k,Sp,F.Lt,Sp,Mul(D(2),n))),
                Sp,new Formula.Absolute(lk)))]);
    }

    private static Formula ParsevalFormula()
    {
        var k=F.Id("k"); var bound=Mul(D(2),F.Id("n"));
        var ck=At(F.Id("c"),k); var lk=At(LambdaLower,k);
        var weighted=SumBelow("k",bound,Mul(Square(lk),Square(ck)));
        return new Formula.Aligned([
            Eq(Mul(Square(Alpha),Square(new Formula.Norm(F.Id("u")))),
                Mul(Square(Alpha),SumBelow("k",bound,Square(ck)))),
            Le(Mul(Square(Alpha),SumBelow("k",bound,Square(ck))),weighted),
            Seq(Eq(weighted,Square(new Formula.Norm(At(F.Id("H"),F.Id("u"))))),
                Sp,F.Eq,Sp,D(1))]);
    }

    private static Formula SpectralResidualFormula()
    {
        var z=F.Id("z"); var abs=new Formula.Absolute(LambdaLower);
        return new Formula.Aligned([
            Eq(At(F.Id("H"),z),Mul(LambdaLower,z)),
            new Formula.Relation(z,FormulaRelationOperator.NotEqual,D(0)),
            Eq(abs,Alpha),
            Le(Mul(abs,new Formula.Norm(At(F.Id("G"),F.Id("v")))),D(1))]);
    }

    private static Formula RepeatedWindowSpectralFormula()
    {
        var q=F.Id("q"); var n=F.Id("n"); var abs=new Formula.Absolute(LambdaLower);
        var size=Mul(D(2),n); var gv=At(F.Id("G"),F.Id("v"));
        var minimum=Seq(new Formula.Subscript(Min,
            Seq(Mu,Sp,InMacro,Sp,Call("Spec",F.Id("H")))),Sp,new Formula.Absolute(Mu));
        return new Formula.Aligned([
            Seq(Le(Mul(abs,Mul(q,Add(q,D(1)))),Mul(Mul(size,abs),new Formula.Norm(gv))),
                Sp,F.Le,Sp,size),
            Seq(Eq(DeltaLower,minimum),Sp,F.Eq,Sp,abs,Sp,F.Le,Sp,
                Div(size,Mul(q,Add(q,D(1)))))]);
    }

    private static Formula Square(Formula x) => new Formula.Power(x,D(2));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
        StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), role);

    private static Formula FullInverseEstimate()
    {
        var v=F.Id("v"); var q=F.Id("q"); var n=F.Id("n");
        return And(Eq(new Formula.Norm(v),D(1)),
            Le(Mul(q,Add(q,D(1))),Mul(Mul(D(2),n),new Formula.Norm(At(F.Id("G"),v)))));
    }

    private static Formula EntryFormula()
    {
        var t = F.Id("t"); var l = F.Id("l"); var d = F.Id("d");
        return All("t", Arrow(N(), R()), All("l", N(), All("d", N(), And(
            Eq(E(t,l,D(0)), Div(D(1), At(t,Mul(D(2),l)))),
            Eq(E(t,l,Add(d,D(1))), Div(
                Mul(E(t,l,d),At(t,Add(Mul(D(2),Add(l,d)),D(1)))),
                At(t,Mul(D(2),Add(Add(l,d),D(1))))))))));
    }

    private static Formula BlockFormula()
    {
        var t = F.Id("t"); var n = F.Id("n"); var i = F.Id("i"); var j = F.Id("j");
        var iv = Call("val",i); var jv = Call("val",j);
        return All("t", Arrow(N(),R()), All("n",N(), All("i",Call("Fin",n),
            All("j",Call("Fin",n), Eq(At(Call("L",t,n),i,j),
                Call("ite",Eq(i,j),At(t,Mul(D(2),iv)),
                    Call("ite",Eq(Add(jv,D(1)),iv),
                        new Formula.Negate(At(t,Add(Mul(D(2),jv),D(1)))),D(0))))))));
    }

    private static Formula MassFormula()
    {
        var t = F.Id("t"); var q = F.Id("q"); var i = F.Id("i");
        var l = F.Id("l"); var d = F.Id("d");
        var size = Add(Mul(D(2),q),D(1));
        var inverse = new Formula.Power(Call("L",t,size), new Formula.Negate(D(1)));
        Formula Index(Formula x) => Seq(Langle,Sp,x,Sp,Rangle);
        Formula Entry(Formula row, Formula col) => At(inverse,Index(row),Index(col));
        var summand = Add(Entry(Add(Add(l,d),D(1)),l),
            Entry(Add(Add(Add(q,l),d),D(1)),Add(Add(q,l),D(1))));
        var sum = SumBelow("l",q,SumBelow("d",Sub(q,l),summand));
        var positive = All("i",N(),Lt(D(0),At(t,i)));
        var bounded = All("i",N(),Le(At(t,i),D(1)));
        var repeated = All("i",N(),Implies(Lt(i,Mul(D(2),q)),
            Eq(At(t,Add(i,size)),At(t,i))));
        return All("t",Arrow(N(),R()),All("q",N(),Implies(positive,
            Implies(bounded,Implies(repeated,Le(Mul(q,Add(q,D(1))),sum))))));
    }

    private static Formula E(Formula t, Formula l, Formula d) => Call("E",t,l,d);
    private static Formula N() => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula R() => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f,[.. xs]);
    private static Formula Call(string name, params Formula[] xs) => At(Seq(Operatorname,Grp(F.Id(name))),xs);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula SumBelow(string name, Formula bound, Formula body) =>
        Seq(new Formula.Subscript(Sum,Seq(F.Id(name),Sp,F.Lt,Sp,bound)),Sp,Grp(body));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Subtract,b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a,b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
}
