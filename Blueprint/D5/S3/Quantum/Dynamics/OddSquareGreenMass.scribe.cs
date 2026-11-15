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
                + "The theorem alone does not assert a Tribonacci prefix spectral bound. The application "
                + "below also uses the exact word-to-hopping correspondence and aligned repeated windows. "
                + "No infinite-volume spectrum, localization, quasimode or "
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
                + "finite positive open chain. The final application identifies the actual Tribonacci "
                + "hoppings and windows under this same index convention. Entropy requires a "
                + "separate physical-state and spatial-cut argument.")))),
            SpectralApplication(),
            TribonacciApplication())));

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
            + "conversion from full-inverse mass to a spectral bound. The same entrywise formula "
            + "defines a Hermitian matrix on C^(2n): its real orthonormal eigenbasis is also a "
            + "complex orthonormal eigenbasis with the same real eigenvalues. Thus the spectral "
            + "distance is unchanged when the scalar field is extended to C."))));

    private static DocumentBlock TribonacciApplication() => new DocumentBlock.Section(
        H("Application: a uniform spectral bound for actual Tribonacci open prefixes"), Blocks(
        Paragraph(Text(
            "Use the original Tribonacci substitution sigma(A)=AB, sigma(B)=AC, sigma(C)=A "
            + "and its fixed word W, with sites and bonds indexed from zero. Put L_j=length(sigma^j(A)) "
            + "and N_j=2 floor(L_j/2). For 0<rho<1 take t(i)=rho^2, rho or 1 according as "
            + "W(i)=A, B or C. These are the same hoppings rho^(weight(W(i))) with the original "
            + "integer weights 2,1,0 in TribonacciPrefixRefutation. The actual N_j-site matrix "
            + "has zero diagonal, bond t(i) between i and i+1, and no closing bond. Let "
            + "delta(rho,j) be its minimum absolute eigenvalue. For every j>=4, the existing "
            + "aligned-window and inverse-mass results imply:")),
        new DocumentBlock.DisplayFormula(TribonacciRateFormula()),
        Paragraph(Text(
            "This is an application of existing declarations, not a new mathematical declaration. "
            + "The exact window uses k=4 floor((j-4)/4), so k+4<=j<=k+7, and the original "
            + "TribonacciAlignedWindows.seed identity sigma^4(A)=ABAC|ABA|ABA|CAB. Set "
            + "a0=sigma^k(A), b0=sigma^k(B), c0=sigma^k(C), s=length(a0 b0 a0 c0), "
            + "and m=length(a0 b0 a0). Concatenation is indicated by juxtaposition. At levels "
            + "divisible by four these three lengths are odd, since the fourth letter images "
            + "have lengths 13,11,7. Hence s is even and m is odd and at least three. The two "
            + "copies of a0 b0 a0 provide the repeated letters. The nonempty tail c0 a0 b0 "
            + "preserves the whole window after even rounding. The original length_mono and "
            + "length_seven estimates give N_j<=128m and s+2m<=N_j.")),
        Paragraph(Text(
            "Write m=2q+1, s=2a and N_j=2n. Then q>=1 and a+2q+1<=n. Equal repeated "
            + "letters have equal actual hoppings, giving t(2a+i+2q+1)=t(2a+i) for i<2q. "
            + "Use the shifted local block inside the full inverse L(t,n)^(-1), retaining all "
            + "exterior sites. The full-inverse estimate and spectral conversion use the same "
            + "Euclidean unit vector v=(1,...,1)/sqrt(n), and give delta(rho,j)q(q+1)<=N_j. "
            + "The original complex open chain is reached by the even/odd reordering and "
            + "alternating sign conjugation above; neither the boundary nor any hopping changes. "
            + "Finally 9q(q+1)-2(2q+1)^2=(q-1)(q+2)>=0 and N_j<=128(2q+1) give "
            + "N_j delta(rho,j)<=128^2 times 9/2=73728. No optimality is claimed.")),
        Paragraph(Text(
            "Non-erasing substitution beginning with A gives L_j>=j+1, hence N_j>=j. "
            + "For every epsilon>0 choose J=max(4,floor(73728/epsilon)+1). For every j>=J "
            + "and every 0<rho<1, the same bound gives 0<=delta(rho,j)<=73728/N_j<=73728/j "
            + "<epsilon. Thus convergence to zero is uniform over the whole open rho interval; "
            + "the cutoff does not depend on rho. The finite initial values j=1,2,3 need no "
            + "separate estimate for this limit. The degenerate endpoint rho=0 is outside "
            + "the positive-hopping argument. This concerns a single-particle finite open-chain "
            + "spectral distance. It neither constructs a many-body ground state nor determines "
            + "spatial-cut entanglement or Rauzy-boundary dimension."))));

    private static Formula TribonacciRateFormula()
    {
        var rho=F.Id("rho"); var j=F.Id("j");
        var delta=At(F.Id("delta"),rho,j); var count=At(F.Id("N"),j);
        return All("rho",R(),All("j",N(),Implies(And(Lt(D(0),rho),Lt(rho,D(1))),
            Implies(Le(D(4),j),And(Le(D(0),delta),Le(Mul(count,delta),D(7,3,7,2,8)))))));
    }

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
