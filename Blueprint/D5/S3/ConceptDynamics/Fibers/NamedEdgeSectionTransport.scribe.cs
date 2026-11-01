using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Fibers;

internal sealed class NamedEdgeSectionTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Named edge transport retains parallel edges, loops and dependent fibres in the root evaluation criterion.",
        H("Named Edge Section Transport"),
        Blocks(
            Paragraph(Text("Let V and E be arbitrary vertex and named edge types with endpoint maps s,t:E to V. A signed generator is an original named edge or the formal inverse of that same edge. Finite paths use the symmetrified original quiver. No finiteness, simplicity, chosen spanning tree or commutativity assumption is imposed.")),
            Paragraph(Text("Each edge e is represented by the three-segment path s(e), source(e), target(e), t(e). The two ports are distinct constructors and retain the original edge name, including when s(e)=t(e) or another edge has the same endpoints. Write endpoint for this projection to V. EdgeEquivalences(s,t,F) means exactly the family of equivalences F(s(e)) to F(t(e)); EdgeUnitaries means the family of complex linear isometric equivalences. ComplexNormedFibres(V) means a family of normed complex vector spaces indexed by V. These are notation for the full parameter families, not extra hypotheses. The port fibres are the original endpoint fibres. The middle segment carries exactly U(e), the outer segments carry identity maps, and reverse traversal uses the inverse of that same map.")),
            Describe.Lean(
                DescribeId.Create("incidence-path-transport"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport.incidence_path_transport"),
                H("Transport on every actual finite path"),
                StatementSource.FromAuthor(IncidenceStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An outer segment projects to an empty path. A middle segment projects to its signed original generator. Concatenation projects every finite incidence walk, including walks beginning at ports. Each signed original generator lifts to its three-segment path or its reverse. The projection and lift preserve the actual dependent-fibre composite. Projecting a lifted path returns its literal signed original path, retaining the named generators even when their transport operators happen to agree.")))),
            Describe.Lean(
                DescribeId.Create("named-unitary-root-classification"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Fibers/NamedEdgeSectionTransport.named_unitary_root_classification"),
                H("Root evaluation and unitary holonomy"),
                StatementSource.FromAuthor(RootStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Place a normed complex vector space F(v) at each vertex and a linear isometric equivalence U(e) at each named edge. The finite-dimensional unitary setting is obtained by taking the original fibres isometric to the same complex d-space. Connectedness means that every vertex admits an actual finite signed path from the chosen root. Compatible sections satisfy every original named edge equation.")),
                    Paragraph(Text("Extension to the ports and restriction to the original vertices are inverse maps on sections. Projection and lifting identify the common fixed vectors of all root loops. Applying ConfigurationPathTransport.rootSectionMap_bijective to this faithful incidence graph supplies the section bijection. In the formulas, value denotes the underlying vector of a subtype, section denotes its value at a vertex, and inverse denotes the inverse equivalence. The comparison is root evaluation. Its inverse at any vertex is transport along every root-to-vertex path, and the target is the intersection of the kernels of all actual root-loop operators minus the identity.")),
                    Paragraph(Text("Every compatible section has the same norm in each fibre as at the root. The comparison preserves the norm of differences measured in the root fibre. This is the root-fibre metric on sections; no product norm or summability on the vertex set is assumed. Every root vector transports independently of path exactly when every root-loop operator is the identity. Existence of a fixed vector or the zero section does not imply that all-vector condition.")),
                    Paragraph(Text("No assertion is made here about two-cell attaching boundaries or continuous path homotopy. For a simply connected two-dimensional cell complex, passing from flat attaching faces to identity transport on every loop requires a separate topological correspondence. Local face flatness on a punctured region does not supply that correspondence, and nontrivial holonomy around its hole remains possible.")))))));

    private static Formula C(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula I(string name) => F.Id(name);
    private static Formula A(Formula f, params Formula[] args) => C("Apply", [f, .. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, I(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Open, Exists, Sp, I(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula R(Formula a, Formula relation, Formula b) =>
        Seq(Open, a, Sp, relation, Sp, b, Close);
    private static Formula And(params Formula[] xs) => xs.Aggregate((a,b) => R(a,Land,b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Params(bool unitary, Formula body) =>
        All("V",C("Type"),All("E",C("Type"),
        All("s",Arrow(I("E"),I("V")),All("t",Arrow(I("E"),I("V")),
        All("F",unitary ? C("ComplexNormedFibres",I("V")) : Arrow(I("V"),C("Type")),
        All("U",C(unitary ? "EdgeUnitaries" : "EdgeEquivalences",I("s"),I("t"),I("F")),body))))));
    private static Formula P(Formula a, Formula b) => C("NamedPath",I("s"),I("t"),a,b);
    private static Formula S(Formula sigma, Formula a) => C("section",sigma,a);
    private static Formula Value(Formula x) => C("value",x);
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula IncidenceStatement()
    {
        var graph = C("incidenceGraph",I("s"),I("t"));
        var transport = C("incidenceTransport",I("U"));
        var p = I("p");
        var projected = All("a",C("IncidenceVertex",I("V"),I("E")),
            All("b",C("IncidenceVertex",I("V"),I("E")),
            All("p",C("Walk",graph,I("a"),I("b")),
                R(C("namedTransport",I("U"),C("projectWalk",p)),Eq,C("walk",transport,p)))));
        var lifted = All("a",I("V"),All("b",I("V"),All("p",P(I("a"),I("b")),
            R(C("walk",transport,C("liftPath",p)),Eq,C("namedTransport",I("U"),p)))));
        var exactWord = All("a",I("V"),All("b",I("V"),All("p",P(I("a"),I("b")),
            R(C("projectWalk",C("liftPath",p)),Eq,p))));
        return Disp(Params(false,And(projected,lifted,exactWord)));
    }
    private static Formula RootStatement()
    {
        var r = I("r"); var a = I("a"); var x = I("x");
        var sigma = I("sigma"); var tau = I("tau"); var ev = I("ev");
        var sections = C("NamedSection",C("underlying",I("U")));
        var kernel = C("holonomyKernel",I("U"),r);
        var op = C("unitaryTransport",I("U"),I("p"));
        var evaluation = All("sigma",sections,R(Value(A(ev,sigma)),Eq,S(sigma,r)));
        var path = All("x",kernel,All("a",I("V"),All("p",P(r,a),
            R(S(A(C("inverse",ev),x),a),Eq,A(op,Value(x))))));
        var norm = All("sigma",sections,All("a",I("V"),
            R(Norm(S(sigma,a)),Eq,Norm(S(sigma,r)))));
        var difference = All("sigma",sections,All("tau",sections,
            R(Norm(R(Value(A(ev,sigma)),Minus,Value(A(ev,tau)))),Eq,
                Norm(R(S(sigma,r),Minus,S(tau,r))))));
        var independent = All("a",I("V"),All("p",P(r,a),All("q",P(r,a),All("x",A(I("F"),r),
            R(A(op,x),Eq,A(C("unitaryTransport",I("U"),I("q")),x))))));
        var trivial = All("p",P(r,r),R(op,Eq,C("LinearIsometryIdentity",A(I("F"),r))));
        var connected = All("a",I("V"),C("Nonempty",P(r,a)));
        return Disp(Params(true,All("r",I("V"),R(connected,Implies,
            Ex("ev",C("Equiv",sections,kernel),And(evaluation,path,norm,difference,R(independent,Iff,trivial)))))));
    }
}
