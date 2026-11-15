using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Routing;

internal sealed class HannUniformSectionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Routing/HannUniformSection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real probability section of the original signed Hann records has uniform laws at both endpoints and a nonempty zero-sum subset whenever zero is feasible.",
        H("Uniform original-leaf endpoints"),
        Blocks(
            Def("uniform-real-section", "Section", "The original real probability section",
                "Fix a natural height n, one heterogeneous assignment q on Router n in [-1/2,1], "
                + "and one qutrit bus. Section n q bus consists of the real z for which there is "
                + "p:Address n to Real with p(a)>=0, sum p=1, and synthesis(p)=z vacuumRecord. "
                + "Address 0 is Unit and Address(n+1)=Bool times Address n, so there are exactly "
                + "2^n original leaves. The synthesis is the sum of p(a) record(n,q,bus,a) using "
                + "the actual HannSignedCertificate record and vacuumRecord, with real scalars "
                + "cast to Complex. In the formulas, ofRealCoefficients denotes this pointwise cast. "
                + "Probability is assigned only to these original leaves."),
            Def("uniform-real-local", "RealLocal", "The real local clauses",
                "At q=1 the root scalar is the sum of the two child scalars. At q=-1/2 both "
                + "child scalars are minus the root scalar. At every other q all three vanish. "
                + "These are exactly the real restrictions of HannExactForest.Local."),
            Def("uniform-real-equations", "RealEquations", "Exact real coordinates of the original matrix",
                "At height zero equate the distinct node and original-leaf coordinates. At each "
                + "successor impose RealLocal and recurse with the same q restricted by "
                + "restrict n q b. Casting every real coordinate to Complex gives exactly "
                + "HannExactForest.Equations. Its existing kernel_iff_equations identifies these "
                + "clauses with the literal matrix kernel. The existing relation_iff_matrix_kernel "
                + "then gives both directions of the original loaded-record relation. Taking real "
                + "parts of a complex lift produces a real lift because every matrix coefficient "
                + "is real. No rows, columns, addresses, root equations or mass variables are added."),
            Describe.Lean(DescribeId.Create("binary-conformal-original-kernel"),
                DeclarationHandle.Create(Module + "binary_conformal_kernel"),
                H("Binary leaves and signed unit nodes"),
                StatementSource.FromAuthor(BinaryStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any real q, a kernel vector with nonnegative nonzero original leaves "
                    + "contains a nonzero binary-leaf kernel certificate. A selected leaf had "
                    + "strictly positive original mass. Its node entries are zero or signed units "
                    + "with the original signs; the root has exactly the original root sign. "
                    + "The recursive construction rounds the root to its sign. At an upper router "
                    + "with nonzero root, one child with the required sign suffices. With zero root, "
                    + "the rounded child signs cancel. At a lower router, both child signs equal "
                    + "the negative root sign. At an interior router all local roots vanish. "
                    + "Combining the literal child coordinates preserves all original clauses. "
                    + "If all leaves vanished, induction would force every node to vanish; hence "
                    + "a selected nonzero root also ensures nonempty leaves.")))),
            Def("uniform-certificate", "UniformCertificate", "Nonempty original-leaf sums",
                "UniformCertificate n q bus S e means that S is a nonempty finite subset of "
                + "Address n, e is -1, 0 or 1, and the sum of the original records over S is "
                + "e vacuumRecord. Dividing by card S gives a probability law uniform on S "
                + "and the feasible scalar e/card S."),
            Def("uniform-endpoint", "UniformEndpoint", "Uniform endpoint values",
                "UniformEndpoint n q bus z provides such an S and e with z=e/card S and "
                + "1<=card S<=2^n. Different endpoints may use different subsets and signs."),
            Describe.Lean(DescribeId.Create("original-positive-support-zero-certificate"),
                DeclarationHandle.Create(Module + "zero_certificate"),
                H("Zero-sum subset in the given positive support"),
                StatementSource.FromAuthor(ZeroStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Lift the given nonnegative normalized p through the original matrix theorem. "
                    + "The real root is zero, so the binary certificate also has zero root. "
                    + "Its leaves equal one on a nonempty subset S and zero elsewhere. The exact "
                    + "matrix bridge therefore gives sum over S of record(a)=0. Every selected "
                    + "leaf belongs to the positive support of the given p. The argument does "
                    + "not require zero to be an endpoint of the section.")))),
            Describe.Lean(DescribeId.Create("complete-original-uniform-section"),
                DeclarationHandle.Create(Module + "uniform_section"),
                H("The complete closed interval and both uniform endpoints"),
                StatementSource.FromAuthor(SectionStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Apply the existing signConformalGlobalKernelCircuitDecomposition to the "
                    + "same real original matrix, reindexing only its rows by Fin(card Row). "
                    + "Every summand is conformal to the given probability lift, so its leaves "
                    + "are nonnegative. A nonzero summand has a nonzero leaf. Apply binary rounding "
                    + "to that circuit. The rounded vector has support contained in the circuit. "
                    + "Subtract the original value at a selected leaf times the rounded vector. "
                    + "The difference remains in the kernel, stays inside the circuit support, "
                    + "and vanishes at that leaf. Support minimality forces the difference to be "
                    + "zero. Thus every circuit is a positive scalar times a binary certificate. "
                    + "After normalization, its contribution has weight t card S and value "
                    + "e/card S. The weights sum to one, and their weighted values sum to z. "
                    + "Consequently the section lies in the convex hull of its uniform values. "
                    + "Conversely every uniform value is feasible and the section is convex. "
                    + "There are finitely many subsets and three possible numerators. If any "
                    + "value is feasible, the least and greatest uniform values are feasible, "
                    + "bound the whole section, and convexity fills their closed interval. "
                    + "This treats both signs and both endpoints together, including a singleton.")))),
            Paragraph(Text(
                "The small-height boundaries distinguish emptiness, a singleton and two "
                + "different endpoint values. At height zero the section is {1}. At height one, "
                + "a strictly interior root rate gives the empty section, while rate -1/2 gives "
                + "{-1/2}. At rate 1, the unequal leaf probabilities 2/3 and 1/3 are feasible. "
                + "For a larger example, let q3 have height three, root rate 1, all left-subtree "
                + "rates -1/2 and all right-subtree rates 1. Its nonnegative kernel coordinates "
                + "satisfy mass/4 <= root <= mass, with the bounds attained by four equal left "
                + "leaves and by one right leaf. Form q4 by placing rate -1/2 above two identical "
                + "copies of q3, and q5 by placing rate -1/2 above two copies of q4. Their sections "
                + "for the wait bus are exactly [-1/2,-1/8] and [1/16,1/4], respectively. "
                + "Duplicating a normalized leaf law with half its mass in each copy sends its "
                + "root value z to -z/2. Conversely the lower-router equations equate both child "
                + "roots to minus the parent root; the two child mass bounds give the displayed "
                + "parent bounds. Convexity fills the intervals between the attained endpoints.")),
            Paragraph(Text(
                "The conformal-decomposition method is classical; the elementary-vector source "
                + "is Mueller and Regensburger, Elementary vectors and conformal sums in polyhedral "
                + "geometry and their relevance for metabolic pathway analysis, Section 3.1, "
                + "Lemma 2 and Theorem 3. The binary rounding and its application here concern "
                + "the stated signed Hann model. No claim about physical signed channels, "
                + "hardware, complexity, ontology or originality follows. A feasible probability "
                + "law need not itself be uniform.")))));

    private static DocumentBlock Def(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula I(string x) => F.Id(x);
    private static Formula C(string x, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(x), [.. a]);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula All(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Ex(string x, Formula t, Formula b) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(x), t)], b);
    private static Formula Arr(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a,op,b);
    private static Formula Eq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a, Formula b) => Rel(a,FormulaRelationOperator.NotEqual,b);
    private static Formula Leq(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a, Formula b) => Rel(a,FormulaRelationOperator.LessThan,b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(a,op,b);
    private static Formula And(Formula a, Formula b) => Logic(a,FormulaLogicOperator.And,b);
    private static Formula Or(Formula a, Formula b) => Logic(a,FormulaLogicOperator.Or,b);
    private static Formula Imp(Formula a, Formula b) => Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Both(params Formula[] a) => System.Linq.Enumerable.Aggregate(a,And);
    private static Formula SumOver(string a, Formula s, Formula body) => Seq(Sum,Underscore,Grp(I(a),InMacro,Sp,s),Grp(body));
    private static Formula Real => I("Real");
    private static Formula N => I("n");
    private static Formula Q => I("q");
    private static Formula Bus => I("bus");
    private static Formula Addr => C("Address",N);
    private static Formula Nodes => C("Node",N);
    private static Formula Rates => All("v",C("Router",N),Both(
        Leq(C("neg",new Formula.Fraction(D(1),D(2))),App(Q,I("v"))),Leq(App(Q,I("v")),D(1))));
    private static Formula Parameters(Formula body, bool bus=true) => All("n",I("Nat"),
        All("q",Arr(C("Router",N),Real),bus ? All("bus",I("Qutrit"),Imp(Rates,body)) : body));
    private static Formula Kernel(Formula x, Formula c) => Eq(C("mulVec",C("matrix",N,Q),C("SumElim",x,c)),D(0));
    private static Formula ZeroSum(Formula s) => Eq(SumOver("a",s,C("record",N,Q,Bus,I("a"))),D(0));

    private static Formula BinaryStatement()
    {
        Formula x=I("x"),c=I("c"),u=I("u"),d=I("d"),a=I("a"),v=I("v"),root=C("root",N);
        Formula conclusion=Ex("u",Arr(Addr,Real),Ex("d",Arr(Nodes,Real),Both(Kernel(u,d),Ne(u,D(0)),
            All("a",Addr,Or(Eq(App(u,a),D(0)),Eq(App(u,a),D(1)))),
            All("a",Addr,Imp(Ne(App(u,a),D(0)),Lt(D(0),App(x,a)))),
            All("v",Nodes,Or(Eq(App(d,v),D(0)),Or(Eq(App(d,v),C("neg",D(1))),Eq(App(d,v),D(1))))),
            All("v",Nodes,Imp(Ne(App(d,v),D(0)),Eq(C("sign",App(d,v)),C("sign",App(c,v))))),
            Eq(C("sign",App(d,root)),C("sign",App(c,root))))));
        return Parameters(All("x",Arr(Addr,Real),All("c",Arr(Nodes,Real),
            Imp(Both(All("a",Addr,Leq(D(0),App(x,a))),Ne(x,D(0)),Kernel(x,c)),conclusion))),false);
    }
    private static Formula ZeroStatement()
    {
        Formula p=I("p"),a=I("a"),s=I("S");
        Formula premise=Both(All("a",Addr,Leq(D(0),App(p,a))),Eq(SumOver("a",Addr,App(p,a)),D(1)),
            Eq(App(C("synthesis",N,Q,Bus),C("ofRealCoefficients",p)),D(0)));
        Formula conclusion=Ex("S",C("Finset",Addr),Both(C("Nonempty",s),
            All("a",s,Lt(D(0),App(p,a))),ZeroSum(s)));
        return Parameters(All("p",Arr(Addr,Real),Imp(premise,conclusion)));
    }
    private static Formula SectionStatement()
    {
        Formula section=C("Section",N,Q,Bus),l=I("l"),r=I("r"),s=I("S");
        Formula interval=Or(Eq(section,I("emptyset")),Ex("l",Real,Ex("r",Real,Both(Leq(l,r),
            Eq(section,C("Icc",l,r)),C("UniformEndpoint",N,Q,Bus,l),C("UniformEndpoint",N,Q,Bus,r)))));
        Formula zero=Imp(C("mem",D(0),section),Ex("S",C("Finset",Addr),Both(C("Nonempty",s),ZeroSum(s))));
        return Parameters(And(interval,zero));
    }
}
