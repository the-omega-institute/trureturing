using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry;

internal sealed class FiniteRelativeConeCollapseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite simplicial cone collapses onto every subcone with the same apex on the original vertex labels.",
        H("Relative collapse of finite cones"),
        Blocks(
            Paragraph(Text("Let V be a finite vertex type and K,L abstract simplicial complexes whose faces are nonempty finite subsets of V. Suppose L is a subcomplex of K. Choose a vertex v such that the singleton face containing v belongs to L and adjoining v to any face of either complex gives another face of that complex.")),
            Describe.Lean(
                DescribeId.Create("finite-relative-cone-collapse"),
                DeclarationHandle.Create("D5/S3/Geometry/FiniteRelativeConeCollapse.exists_sequence"),
                H("Collapse onto an arbitrary common-apex subcone"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Complex(V) denotes PreAbstractSimplicialComplex V, Face(K,s) means s is a face of K, singleton(v) is the singleton finite set, and insert(v,s) adjoins v to s. The order L <= K is inclusion of all faces. Nonempty(Sequence(K,L)) asserts the existence of an inductively constructed finite sequence of actual elementary free pairs, with exact initial complex K and exact terminal complex L.")),
                    Paragraph(Text("Use strong induction on the finite number of faces of the current complex M. When M equals L the empty sequence suffices. Otherwise choose a face of M outside L. Removing v from it leaves a nonempty face outside L: an empty remainder would make the original face the apex singleton, and a remainder in L would put the original face in L by cone closure and downward closure.")),
                    Paragraph(Text("Extend this remainder to a maximal face p of M not containing v. The face p remains outside L by downward closure. Its only strict coface is insert(v,p). Indeed, a strict coface avoiding v contradicts maximality; removing v from any strict coface containing v gives an apex-free face containing p, which maximality forces to equal p. Thus p and insert(v,p) form an elementary free pair.")),
                    Paragraph(Text("Delete this free pair by retaining exactly the faces not containing p. Every face of L is retained, because a face of L containing p would put p in L. The retained complex is still a cone at v: since v is absent from p, adjoining v cannot create containment of p. The face p itself is removed, so the number of faces strictly decreases. Apply the induction hypothesis to the retained complex and prepend this pair.")),
                    Paragraph(Text("The complexes may be nonpure and nonfull, and may have ghost labels. No dimension bound, flag condition, ordering, or previously supplied collapse sequence is required. The case K=L uses the reflexive sequence; an empty vertex type admits no choice of apex. All intermediate complexes keep every face of L and use the original vertex type and its given instances.")),
                    Paragraph(Text("The existing Sequence.realize construction turns the resulting sequence into a relative deformation fixing the whole realization of L. The present statement supplies the combinatorial sequence itself. It gives no bound on sequence-search running time and makes no classification or optimality claim. TauCetiProject/TauCeti, revision 4caf68dc9fe57dcd98422514629aa79c09be1a66, Collapse/Cone.lean, proves the related point-apex collapse IsCone.collapsesTo_point; the target here is an arbitrary subcone with the same apex."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));

    private static Formula Statement()
    {
        var vtype = F.Id("V");
        var k = F.Id("K");
        var l = F.Id("L");
        var v = F.Id("v");
        var s = F.Id("s");
        Formula Cone(Formula c) => All("s", Call("Finset", vtype),
            Imp(Call("Face", c, s), Call("Face", c, Call("insert", v, s))));
        Formula body = Imp(new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, k),
            Imp(Call("Face", l, Call("singleton", v)),
                Imp(Cone(k), Imp(Cone(l), Call("Nonempty", Call("Sequence", k, l))))));
        body = All("K", Call("Complex", vtype), All("L", Call("Complex", vtype),
            All("v", vtype, body)));
        body = Seq(OpenBracket, Call("Fintype", vtype), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", vtype), CloseBracket, Comma, Sp, body);
        return All("u", Call("Universe"), All("V", Call("Type", F.Id("u")), body));
    }
}
