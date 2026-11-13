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
                + "also needs the exact word-to-hopping correspondence, sublattice spectral identification "
                + "and initial short prefixes. No infinite-volume spectrum, localization, quasimode or "
                + "filling hypothesis enters this theorem.", DescribeRole.Theorem),
            H("Application: a Euclidean estimate for the full inverse"),
            Paragraph(Text(
                "Let t be a positive real hopping sequence bounded above by one, and let n,a,q be "
                + "natural numbers with q at least one and a+2q+1 at most n. Assume exactly the "
                + "2q repetitions t(2a+i+2q+1)=t(2a+i), for i<2q. Set G=L(t,n) inverse, acting "
                + "on the Euclidean space R^n, x=(1,...,1) and v=x/sqrt(n). The hypotheses imply n>0. "
                + "The quadratic mass theorem has the following consequence, without a new "
                + "mathematical declaration:")),
            Disp(FullInverseEstimate()),
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
                + "Euclidean consequence of the mass estimate. Identifying the actual hopping "
                + "sequence, reordering the physical symmetric matrix into its sublattices, "
                + "performing the sign conjugation, relating its eigenvalues to the block's "
                + "singular values and treating the short prefixes remain separate obligations. "
                + "No all-prefix Tribonacci spectral rate or entropy law is asserted.")))));

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
