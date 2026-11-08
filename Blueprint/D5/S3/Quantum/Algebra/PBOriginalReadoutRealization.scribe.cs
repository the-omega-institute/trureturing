using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class PBOriginalReadoutRealizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single ambient state gives a coherent reading of every original label, and its selected central sector supplies the actual PB outer budgets.",
        H("Original labels, positive two-tables, and a selected central sector"),
        Blocks(Describe.Lean(DescribeId.Create("original-piecewise"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/PBOriginalReadoutRealization.original_piecewise"),
            H("Coherent realization with zero and nonzero axis branches"),
            StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("OriginalData retains the original real normed label space E, its bilinear Jordan product J, unit u, and arbitrary total response D:E times E to E. Its supplied inclusion i into an arbitrary unital complex C-star algebra A is real linear, isometric and self-adjoint valued, maps u to one, and satisfies i(J(a,b))=(i(a)i(b)+i(b)i(a))/2. E need not be complete or dense in the whole self-adjoint part of A. The original preparation family is arbitrary and its cone is exact: i(a) is positive exactly when every original preparation evaluates a nonnegatively. Every original directed Hermitian two-table is positive semidefinite. No mass is divided or normalized; zero, unequal and subnormalized original masses remain in the domain.")),
                Paragraph(Text("B and C are unital star subalgebras of the same A, C is norm closed, C is contained in B, and every element of C commutes with every element of B. The theorem accepts a specified unital star character chi:C to the complex scalars. Its existence forces this character branch to be proper. Hahn-Banach extends the continuous character functional with its norm preserved. Norm one and value one imply positivity, giving one ambient state phi which retains this chi. The original normalized_gns declaration supplies the norm-one cyclic vector in the completed GNS space. No independent extension is selected for each reading vector.")),
                Paragraph(Text("cyclicSpace(phi,B) is the norm closure of the range of b mapped to pi(b)xi in that one ambient GNS representation. It contains xi and is B invariant. For c in C, retention makes pi(c-chi(c)one)xi have zero squared norm. Centrality propagates this equality along the B orbit and continuity passes it to its closed span, so pi(c)v=chi(c)v for every vector in cyclicSpace. Its real Hilbert space is nontrivial because xi has norm one.")),
                Paragraph(Text("compressedOp sends every original a in E to the orthogonal compression of pi(i(a)) to that single cyclicSpace, regarded as a real linear operator. This map is linear and symmetric on all original labels, including unknown outer D outputs. It reads u as the identity. The known Jordan domain is exactly L=i inverse image of B; invariance proves the Jordan law there. No closure, descent, additivity, homogeneity or extension of D is introduced.")),
                Paragraph(Text("For complex coefficients z and w, the original quadratic label is normSq(z)J(a,a)+normSq(w)J(b,b)+2 Re(conjugate(z)w)J(a,b)+2 Im(conjugate(z)w)D(a,b). Hermitian original tables determine the reversed readings. Their positivity and the exact original cone make this label positive in A. Every mathematical positive functional therefore reads the same whole two-table positively. The determinant gives f(D(a,b)) squared at most f(J(a,a))f(J(b,b))-f(J(a,b)) squared. Applying this to the actual ambient vector expectation and then the compression proves Readout.p2 for every pair of original labels and every vector, including zero. Mathematical vector expectations are not identified with original preparations.")),
                Paragraph(Text("SectorCertificate contains six actual elements xx,yy,dd,xy,xd,yd of C, wired respectively to i(J(x,x)), i(J(y,y)), i(J(D(x,y),D(x,y))), i(J(x,y)), i(J(x,D(x,y))) and i(J(y,D(x,y))). It requires the original x,y,D(x,y) to lie in L. The specified character reads the first three as X squared, Y squared and delta squared, and the last three as zero. Scalarization and the local Jordan law prove the represented square and anticommutation relations. Global ambient anticommutation is not a premise: the three central cross elements may be nonzero globally.")),
                Paragraph(Text("When X=0 or Y=0, raw all-vector P2 forces every diagonal expectation of op(D(x,y)) to vanish. Symmetry makes that operator zero, and its represented square on the nontrivial cyclic space gives delta=0. This branch uses no involutions. When X and Y are both nonzero, normalize only the mathematical represented axes by real scalars to construct Fibre of the same Readout. X and Y may be unequal and delta may be zero. This normalization supplies no new original input, physical inverse or operation.")),
                Paragraph(Text("The nonzero branch directly applies PBActualOuterBudget.actual_outer_budget to this constructed R and Fibre, the same original J,u,D,x,y, original PB and the complete six-field BDerivedInterface. For every real lambda,t with t nonzero and t squared=lambda squared X squared+1, write z=t u+lambda x, nu=D(x,y)-J(x,z), omega=J(x,y)+D(x,z). It obtains one unit vector reading both actual outer original labels D(y+nu,z+omega) and D(y-nu,z-omega), each with squared budget X squared/t squared+delta squared, their difference 2 lambda X squared Y/t, and lambda squared X squared(X squared Y squared-delta squared) at most X squared+delta squared. Omega may be globally nonzero; only its operator reading is killed. Unknown outer D outputs remain original labels and need not belong to L.")),
                Paragraph(Text("For the zero algebra A, faithfulness makes every original label and every original D value zero, independently of a character or normalized state. This is the first conjunct of the theorem. The second conjunct constructs the specified-character realization whenever its premises are supplied.")),
                Paragraph(Text("The abstract JB-to-JC carrier and Albert exclusion, full B183.2/184/185.1, the derivation of SectorCertificate from original PB or orthogonality, source pairwise anticommutation, full raw 200/202, saturation and separation remain separate unpaid boundaries. The six-field BDerivedInterface remains explicit derived debt. This result asserts the conditional realization bridge and its finite actual outer budgets; it supplies neither those source interfaces nor final source-host coverage. No freezing or coverage status is asserted."))),
            DescribeRole.Theorem))));

    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => global::StrataLint.Scribe.DefinitionDsl.Call(s,a);
    private static Formula N(int n) => global::StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula All(string s, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(s),t,b);
    private static Formula Eq(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Equal(a,b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Mul(Formula a, Formula b) => global::StrataLint.Scribe.DefinitionDsl.Multiply(a,b);
    private static Formula Inst(Formula a, Formula b) => Seq(OpenBracket,a,CloseBracket,b);
    private static Formula Statement()
    {
        var A=I("A"); var E=I("E"); var P=I("P"); var O=I("O"); var B=I("B"); var center=I("C");
        var chi=I("chi"); var x=I("x"); var y=I("y"); var X=I("X"); var Y=I("Y"); var delta=I("delta");
        var real=C("Real"); var complex=C("Complex");
        var zero=Imp(C("Subsingleton",A),And(All("a",E,Eq(I("a"),N(0))),
            All("a",E,All("b",E,Eq(C("D",O,I("a"),I("b")),N(0))))));
        var proper=All("chi",C("StarCharacter",center,complex),All("x",E,All("y",E,
            All("X",real,All("Y",real,All("delta",real,
                Imp(C("SectorCertificate",O,B,center,chi,x,y,X,Y,delta),
                    C("Nonempty",C("Realization",O,B,center,chi,x,y,X,Y,delta)))))))));
        var central=All("c",center,All("b",B,Eq(Mul(C("val",I("c")),C("val",I("b"))),
            Mul(C("val",I("b")),C("val",I("c"))))));
        var assumptions=And(C("PB",C("J",O),C("D",O)),And(C("BDerivedInterface",C("J",O),C("u",O),C("D",O)),
            And(C("Closed",center),And(C("Included",center,B),central))));
        var body=All("O",C("OriginalData",A,E,P),All("B",C("StarSubalgebra",complex,A),
            All("C",C("StarSubalgebra",complex,A),Imp(assumptions,And(zero,proper)))));
        body=Inst(C("CstarAlgebra",A),Inst(C("PartialOrder",A),Inst(C("StarOrderedRing",A),
            Inst(C("NormedAddCommGroup",E),Inst(C("NormedSpace",real,E),body)))));
        return All("A",I("Type"),All("E",I("Type"),All("P",I("Type"),body)));
    }
}
