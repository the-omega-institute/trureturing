using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class FinitePhaseAnchorStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The literal finite common-phase probes bound the genuine real Hilbert operator error, with positive contraction and simultaneous finite-menu preservation.",
        H("Finite Phase Anchor Stability"), Blocks(
            Paragraph(Text("The source is Theorem 10.1 of the V79 finite-phase-certificate theory volume, with its standing real dimension 2d, d>=1, positive inner product and orthogonal complex structure. The exact real effect representation has already been obtained from exact binary reversal compatibility. This result starts from that representation; it does not replace exact reversal compatibility by approximate reversal compatibility.")),
            Paragraph(Text("V is any complete real inner product space, with its given norm. An orthonormal basis b indexed by Fin(d) disjoint-union Fin(d) fixes its real dimension to 2d. Write e(i)=b(inl(i)) and f(i)=b(inr(i)); J is a continuous real linear operator, J(Jx)=-x, J*= -J, and J(e(i))=f(i). These assumptions also give J(f(i))=-e(i). The star is the genuine real Hilbert adjoint. Completeness and continuity add no restriction in the source finite dimension.")),
            Describe.Lean(DescribeId.Create("real-readout"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.weight"),
                H("Real effect readout"), StatementSource.FromAuthor(Disp(
                    Space(All("A",Op,All("x",v,Eqn(W(a,x), Inn(x,At(a,x))))),false))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every continuous real linear operator A and every x in V, weight(A,x) is the source real quadratic readout g(x,Ax)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("adjoint-phase-conjugation"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.phaseConjugate"),
                H("True adjoint conjugation"), StatementSource.FromAuthor(Disp(
                    Space(All("J",Op,All("A",Op,Eqn(Call("phaseConjugate",j,a),Seq(StarOf(j),Circ,Sp,a,Circ,Sp,j))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The conjugation is J* composed with A composed with J. Since J*=-J, replacing J* by J would reverse the required sign."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("average-repair"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.repair"),
                H("Common-complex effect repair"), StatementSource.FromAuthor(Disp(
                    Space(All("J",Op,All("A",Op,Eqn(E(a),Mul(Half,Add(a,Call("phaseConjugate",j,a))))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The real-linear map E(A)=repair(J,A) is the average (A+J*AJ)/2. Complex linearity is a conclusion of the theorem."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("literal-anchor-errors"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.AnchorErrors"),
                H("Literal ordered unit probes"), StatementSource.FromAuthor(Disp(
                    Space(All("d",Nat,All("b",Call("OrthonormalBasis",Call("Sum",FinD,FinD),Real,v),All("J",Op,All("A",Op,All("epsilon",Real,
                        new Formula.Logic(Call("AnchorErrors",b,j,a,eps),FormulaLogicOperator.Iff,AnchorFormula())))))),false))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The families are the axis probes e(i), the real bridges (e(i)+e(k))/sqrt(2) for i<k, and the mixed bridges (e(i)+f(k))/sqrt(2) for i<=k. They are all unit vectors by orthonormality. In particular, the diagonal mixed probes are present. The real bridge family and off-diagonal mixed family are empty for d=1. No upper small-error assumption is imposed. The axis family is nonempty because d>=1 and implies epsilon>=0."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-anchor-operator-and-menu-repair"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/FinitePhaseAnchorStability.finite_phase_anchor_repair"),
                H("Finite anchors control the Euclidean operator error and preserve menus"),
                StatementSource.FromAuthor(Disp(MainFormula())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The full telescope is: V in any universe, NormedAddCommGroup V, InnerProductSpace Real V, CompleteSpace V; a natural d with 1<=d; b an OrthonormalBasis (Fin d disjoint-union Fin d) Real V; and J a ContinuousLinearMap Real V V satisfying the three displayed J conditions. The conclusion conjoins the universal individual-effect statement and the universal finite-menu identity. In the individual statement, A is any continuous real linear operator, both A and I-A are positive in mathlib's self-adjoint positive-operator sense, epsilon is any real number, and AnchorErrors is exactly the preceding formula. In the menu identity, iota is any Type with a Fintype instance; no nonemptiness or positivity is needed for that linear identity.")),
                    Paragraph(Text("Every norm of an operator is the continuous real Hilbert operator norm induced by g. A and A-E need only be real-linear. There is no matrix norm instance in the proof. The orthonormal basis expansion, the existing symmetric quadratic row inequality, and mathlib's Rayleigh-quotient norm characterization connect the finite coefficients to this genuine Euclidean norm.")),
                    Paragraph(Text("Set D=A-J*AJ. Its e/e block is S, its e/f and f/e blocks are the same symmetric T, and its f/f block is -S. Axis probes bound the diagonal of S by epsilon. Real bridges bound off-diagonal S by 2 epsilon. Mixed bridges bound off-diagonal T by 2 epsilon and diagonal T by epsilon because the two S diagonal terms cancel. Self-adjoint symmetry supplies the omitted index orders. Each row has two diagonal-sized contributions and 2d-2 remaining contributions, hence absolute sum at most (4d-2)epsilon. Applying the reused quadratic row estimate and Rayleigh theorem gives norm(D)<=(4d-2)epsilon. The identity A-E=D/2 gives the dimension-dependent bound.")),
                    Paragraph(Text("Positivity of A and its conjugate, with both complements positive, bounds every quadratic value of D between minus norm(x)^2 and norm(x)^2. The same Rayleigh theorem gives norm(D)<=1, yielding the independent cap 1/2. This argument includes epsilon=0 and d=1 without division by epsilon or by an off-diagonal count.")),
                    Paragraph(Text("Positive averaging uses mathlib's IsPositive.adjoint_conj, add and nonnegative scalar multiplication. J*J=I makes the map unital. The repaired operator commutes with J and is therefore complex-linear for the inherited action (r+is)x=rx+sJx. Its real self-adjointness together with commutation makes it self-adjoint for the source complex inner product g(x,y)+i g(Jx,y), positive, and a contraction. The displayed vanishing imaginary expectation identifies weight(E,x) with the source complex expectation. The Cauchy-Schwarz readout estimate uses the same operator norm.")),
                    Paragraph(Text("For any finite family with sum A(i)=I, linearity and unitality give sum E(A(i))=I. Applying the individual universal statement to each positive real effect gives all individual bounds simultaneously, with no menu-cardinality factor. The norm of E is at most one because E and I-E are positive; the theorem records those exact effect inequalities.")),
                    Paragraph(Text("This is a source-specific formal synthesis using existing norm and positivity results. It makes no claim of literature novelty, optimal constants, supplied experimental control, or modification of an actual successor. The exact real effect representation, common reference, and preparation/measurement supply remain inherited assumptions."))), DescribeRole.Theorem))));

    private static readonly Formula v=F.Id("V"), d=F.Id("d"), b=F.Id("b"), j=F.Id("J"),
        a=F.Id("A"), x=F.Id("x"), i=F.Id("i"), k=F.Id("k"), eps=F.Id("epsilon");
    private static Formula Zero => new Formula.Number(0);
    private static Formula One => new Formula.Number(1);
    private static Formula Two => new Formula.Number(2);
    private static Formula Half => new Formula.Fraction(One,Two);
    private static Formula Real => Call("Real");
    private static Formula Nat => Call("Nat");
    private static Formula FinD => Call("Fin",d);
    private static Formula Op => Call("ContinuousLinearMap",Real,v,v);
    private static Formula All(string n, Formula t, Formula q) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),t,q);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f,[..args]);
    private static Formula Add(Formula p, Formula q) => new Formula.Binary(p,FormulaBinaryOperator.Add,q);
    private static Formula Sub(Formula p, Formula q) => new Formula.Binary(p,FormulaBinaryOperator.Subtract,q);
    private static Formula Mul(Formula p, Formula q) => new Formula.Binary(p,FormulaBinaryOperator.Multiply,q);
    private static Formula Eqn(Formula p, Formula q) => new Formula.Relation(p,FormulaRelationOperator.Equal,q);
    private static Formula Leq(Formula p, Formula q) => new Formula.Relation(p,FormulaRelationOperator.LessThanOrEqual,q);
    private static Formula Lt(Formula p, Formula q) => new Formula.Relation(p,FormulaRelationOperator.LessThan,q);
    private static Formula And(Formula p, Formula q) => new Formula.Logic(p,FormulaLogicOperator.And,q);
    private static Formula Imp(Formula p, Formula q) => new Formula.Logic(p,FormulaLogicOperator.Implies,q);
    private static Formula Negate(Formula p) => new Formula.Negate(p);
    private static Formula Abs(Formula p) => Seq(Lvert,p,Rvert);
    private static Formula Inn(Formula p,Formula q) => Seq(Langle,Sp,p,Comma,q,Rangle,Underscore,Grp(Mathbb,Grp(F.Id("R"))));
    private static Formula StarOf(Formula p) => new Formula.Power(p,Star);
    private static Formula Axis(Formula t) => At(b,Call("inl",t));
    private static Formula ImagAxis(Formula t) => At(b,Call("inr",t));
    private static Formula Bridge(Formula p,Formula q) => Mul(new Formula.Fraction(One,Call("sqrt",Two)),Add(p,q));
    private static Formula W(Formula p,Formula q) => Call("weight",p,q);
    private static Formula E(Formula p) => Call("repair",j,p);
    private static Formula Error(Formula p) => Abs(Sub(W(a,p),W(a,At(j,p))));
    private static Formula Positive(Formula p) => Call("IsPositive",p);
    private static Formula Budget => Call("min",Half,Mul(Sub(Mul(Two,d),One),eps));
    private static Formula SumI(Formula p) => Seq(Sum,Underscore,Grp(i),p);
    private static Formula AnchorFormula() =>
        And(All("i",FinD,Leq(Error(Axis(i)),eps)),
            And(All("i",FinD,All("k",FinD,Imp(Lt(i,k),Leq(Error(Bridge(Axis(i),Axis(k))),eps)))),
                All("i",FinD,All("k",FinD,Imp(Leq(i,k),Leq(Error(Bridge(Axis(i),ImagAxis(k))),eps))))));
    private static Formula Space(Formula body,bool complete=true) =>
        All("V",Call("Type",F.Id("u")),Seq(OpenBracket,Call("NormedAddCommGroup",v),CloseBracket,
            OpenBracket,Call("InnerProductSpace",Real,v),CloseBracket,
            complete ? Seq(OpenBracket,Call("CompleteSpace",v),CloseBracket,body) : body));
    private static Formula MainFormula()
    {
        Formula effect=All("A",Op,Imp(And(Positive(a),Positive(Sub(One,a))),
            All("epsilon",Real,Imp(Call("AnchorErrors",b,j,a,eps),
                And(Positive(E(a)),And(Positive(Sub(One,E(a))),And(Leq(new Formula.Norm(E(a)),One),
                    And(All("x",v,Eqn(At(E(a),At(j,x)),At(j,At(E(a),x)))),
                        And(Leq(new Formula.Norm(Sub(a,E(a))),Budget),
                            And(All("x",v,Eqn(Inn(At(j,x),At(E(a),x)),Zero)),
                                All("x",v,Leq(Abs(Sub(W(a,x),W(E(a),x))),Mul(Budget,new Formula.Power(new Formula.Norm(x),Two))))))))))))));
        Formula iota=F.Id("iota"), menu=F.Id("menu");
        Formula menus=All("iota",Call("Type",F.Id("w")),Seq(OpenBracket,Call("Fintype",iota),CloseBracket,
            All("menu",Seq(iota,To,Op),Imp(Eqn(SumI(At(menu,i)),One),
                Eqn(SumI(E(At(menu,i))),One)))));
        Formula assumptions=And(All("x",v,Eqn(At(j,At(j,x)),Negate(x))),
            And(Eqn(StarOf(j),Negate(j)),All("i",FinD,Eqn(At(j,Axis(i)),ImagAxis(i)))));
        return Space(
            All("d",Nat,Imp(Leq(One,d),All("b",Call("OrthonormalBasis",Call("Sum",FinD,FinD),Real,v),
                All("J",Op,Imp(assumptions,And(effect,menus)))))));
    }
}
