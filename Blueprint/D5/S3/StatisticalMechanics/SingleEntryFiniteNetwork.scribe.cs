using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class SingleEntryFiniteNetworkDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/SingleEntryFiniteNetwork.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict pair association in a finite Boolean single-entry network.",
        H("Positive pair residuals in arbitrary finite dimension"), Blocks(
            Node("Rates", "Independent positive transition rates",
                "The finite site set I carries arbitrary strictly positive binding rates a_i and unbinding rates b_i. The strictly positive rates eta and theta describe entry to and return from the inhibited state.", DescribeRole.Definition),
            Node("generator", "The actual generator",
                "The states are one inhibited state R and all subsets S of the finite set I. Each site absent from S is inserted at rate a_i; each present site is erased at rate b_i. Only the empty subset enters R, at rate eta, and R returns only to the empty subset, at rate theta. The displayed edge sum uses positive square roots, whose squares are exactly the specified rates; zero edge terms for already present sites contribute no transition.", DescribeRole.Definition),
            Node("ForwardSolution", "The independently anchored law",
                "A curve starts at unit mass in R and satisfies every coordinate of p'=Qp for the stated generator on the nonnegative half-line. Neither positivity nor association is imposed as a premise.", DescribeRole.Definition),
            Node("backward", "The observable generator",
                "The backward generator is the sum, over the actual jumps from a state, of rate times change in the observable.", DescribeRole.Definition),
            Node("activeMass", "Active mass",
                "The sum of the probabilities of all Boolean configurations. Conservation identifies it with r(t)=1-p_R(t).", DescribeRole.Definition),
            Node("occupancy", "Actual site indicator",
                "The indicator of i being a member of the occupied subset. Its value at R is zero.", DescribeRole.Definition),
            Node("margin", "Actual one-site marginal",
                "X_i(t) is the expectation of the same actual occupancy indicator under the full-chain law.", DescribeRole.Definition),
            Node("joint", "Actual two-site marginal",
                "K_ij(t) is the expectation of the product of the actual indicators for sites i and j under that same law.", DescribeRole.Definition),
            Node("association", "Conditional association residual",
                "Delta_ij=r K_ij-X_i X_j, with all quantities evaluated in one common full-chain trajectory.", DescribeRole.Definition),
            Node("fiberWidth", "Four-constraint fiber width",
                "w_ij=min{X_i,X_j,r-X_i,r-X_j}. These are the four actual marginal constraints of the conditional two-site probability table.", DescribeRole.Definition),
            Node("canonicalTrajectory", "An existing probability solution",
                "The (x,R) coordinate of exp(tQ) supplies a forward solution. A scalar diagonal shift and the exponential series prove entrywise nonnegativity; the edge generator conserves total mass.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("single-entry-finite-dual-backward"),
                DeclarationHandle.Create(Prefix + "dual_backward"), H("Forward and backward observable generators agree"),
                StatementSource.FromAuthor(DualStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite site type, every rate tuple, every observable f and every vector p on the actual states, the sum of f(x)(Qp)(x) equals the sum of (backward f)(x)p(x). Expanding the actual two-way edge sum and reindexing insertion against erasure proves this identity. The formula is algebraic and does not require p to be a probability law."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("single-entry-finite-strict-pair"),
                DeclarationHandle.Create(Prefix + "finite_network_strict_pair"),
                H("Every distinct site pair has strictly positive association"),
                StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite site type, every positive rate tuple, every forward solution starting at R, every pair of distinct sites and every t>0, the active mass equals 1-p_R and the active mass, fiber width, association residual and net return theta p_R-eta p_empty are strictly positive. A probability-valued forward solution exists for the same rate tuple. The conclusion supplies coordinatewise convergence of that same trajectory to a stationary vector L of the full generator, the stationary pair identity K_ij(L)=r(L)(a_i/(a_i+b_i))(a_j/(a_j+b_j)), and the exact differential equation Delta_ij'=-(a_i+b_i+a_j+b_j)Delta_ij+(theta p_R-eta p_empty)K_ij on the nonnegative half-line. To obtain the strict input, conjugate the actual edge generator by the product of the independent square-root balance weights. Its negative becomes the Gram matrix of the actual edge incidences. The spectral decomposition of this same trajectory gives a decreasing return probability; its R diagonal is theta>0. Summing the true generator against the one-site and two-site indicators gives the moment equations. Scalar integrating factors then establish the occupied and vacant margins, joint occupancy and association signs. Arbitrary other sites are marginalized without adding a label. Distinct sites imply that the finite set has at least two elements. This statement establishes all pair residuals in arbitrary finite dimension; it does not identify the common slow eigenvalue or its coefficient, and it does not assert all incomparable-configuration minors."))), DescribeRole.Theorem))));

    private static DocumentBlock Node(string declaration, string title, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("single-entry-finite-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula Call(string name, params Formula[] args)
    {
        var list = new System.Collections.Generic.List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) { list.Add(Comma); list.Add(Sp); } list.Add(args[i]); }
        list.Add(Close); return Seq(list.ToArray());
    }
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula Pos(Formula x) => Rel(D(0), FormulaRelationOperator.LessThan, x);
    private static Formula Nonneg(Formula x) => Rel(D(0), FormulaRelationOperator.LessThanOrEqual, x);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), domain, body);
    private static Formula Ex(string v, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(v), domain, body);
    private static Formula Conj(params Formula[] clauses) { var r = clauses[clauses.Length-1]; for (var i=clauses.Length-2;i>=0;i--) r=And(clauses[i],r); return r; }
    private static Formula DualStatement()
    {
        Formula I=F.Id("I"), k=F.Id("k"), f=F.Id("f"), p=F.Id("p"), x=F.Id("x");
        Formula real=Seq(Mathbb,Grp(F.Id("R"))), states=Call("Option",Call("Finset",I)), vector=Seq(states,To,real);
        Formula lhs=Seq(new Formula.Subscript(Sum,Seq(x,Colon,states)),Sp,Mul(Call("f",x),Call("mulVec",Call("generator",k),p,x)));
        Formula rhs=Seq(new Formula.Subscript(Sum,Seq(x,Colon,states)),Sp,Mul(Call("backward",k,f,x),Call("p",x)));
        return Disp(All("I",F.Id("FiniteTypes"),All("k",Call("Rates",I),All("f",vector,All("p",vector,Rel(lhs,FormulaRelationOperator.Equal,rhs))))));
    }
    private static Formula Statement()
    {
        Formula I=F.Id("I"), k=F.Id("k"), p=F.Id("p"), i=F.Id("i"), j=F.Id("j"), t=F.Id("t"), u=F.Id("u"), q=F.Id("q"), x=F.Id("x");
        Formula real=Seq(Mathbb,Grp(F.Id("R"))), states=Call("Option",Call("Finset",I)), curve=Seq(real,To,states,To,real);
        Formula flux=Sub(Mul(Call("theta",k),Call("p",t,F.Id("none"))),Mul(Call("eta",k),Call("p",t,Call("some",F.Id("empty")))));
        Formula fu=Sub(Mul(Call("theta",k),Call("p",u,F.Id("none"))),Mul(Call("eta",k),Call("p",u,Call("some",F.Id("empty")))));
        Formula s=Add(Add(Add(Call("a",k,i),Call("b",k,i)),Call("a",k,j)),Call("b",k,j));
        Formula ode=All("u",real,Imp(Nonneg(u),Call("HasDerivAt",Call("associationCurve",p,i,j),
            Add(Mul(Sub(D(0),s),Call("association",p,i,j,u)),Mul(fu,Call("joint",p,i,j,u))),u)));
        Formula exists=Ex("q",curve,And(Call("ForwardSolution",k,q),All("u",real,Imp(Nonneg(u),And(
            All("x",states,Nonneg(Call("q",u,x))),Rel(Add(Call("q",u,F.Id("none")),Call("activeMass",q,u)),FormulaRelationOperator.Equal,D(1)))))));
        Formula L=F.Id("L");
        Formula limit=Ex("L",Seq(states,To,real),And(All("x",states,Call("Tendsto",Call("coordinateCurve",p,x),F.Id("atTop"),Call("nhds",Call("L",x)))),
            And(Rel(Call("mulVec",Call("generator",k),L),FormulaRelationOperator.Equal,D(0)),
                Rel(Call("joint",Call("constant",L),i,j,D(0)),FormulaRelationOperator.Equal,
                    Mul(Mul(Call("activeMass",Call("constant",L),D(0)),new Formula.Fraction(Call("a",k,i),Add(Call("a",k,i),Call("b",k,i)))),
                        new Formula.Fraction(Call("a",k,j),Add(Call("a",k,j),Call("b",k,j))))))));
        Formula result=Conj(Rel(Call("activeMass",p,t),FormulaRelationOperator.Equal,Sub(D(1),Call("p",t,F.Id("none")))),
            Pos(Call("activeMass",p,t)),Pos(Call("fiberWidth",p,i,j,t)),Pos(Call("association",p,i,j,t)),Pos(flux),ode,limit);
        return Disp(All("I",F.Id("FiniteTypes"),All("k",Call("Rates",I),And(exists,All("p",curve,Imp(Call("ForwardSolution",k,p),
            All("i",I,All("j",I,Imp(Rel(i,FormulaRelationOperator.NotEqual,j),All("t",real,Imp(Pos(t),result)))))))))));
    }
}
