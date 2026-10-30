using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class MultigraphCohomologyContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Incidence/MultigraphCohomologyContraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual rational graph cohomology transports by evacuation of one nonloop edge coefficient, inverse transpose to cycle contraction.",
        H("Cohomology and Coefficient Transport for Multigraph Contraction"),
        Blocks(
            Paragraph(Text("Let G be the existing DirectedMultigraph V E, with arbitrary vertex type V and finite edge type E. "
                + "The boundary, incidence, vertexMap, contract and cycleEquiv are those of MultigraphContraction. "
                + "Fix an edge ID e with source(e) different from target(e). Put F = Surviving e and W = ContractedVertex G e. "
                + "No connectedness, simplicity or condition on bridges is imposed. Loops and parallel surviving IDs persist; "
                + "isolated vertices remain except for the contracted target, and F may be empty.")),
            Describe.Lean(DescribeId.Create("native-cohomology"), DeclarationHandle.Create(Prefix + "coboundary"),
                H("Actual coboundaries and their quotient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("coboundary G sends a vertex function k to the edge function "
                    + "f ↦ k(target(f)) − k(source(f)). Cohomology G is the native rational vector-space quotient "
                    + "(E → Q) / range(coboundary G). Write d(G,k) for this coboundary and class(G,a) for the quotient projection. "
                    + "The values of a vertex function at isolated vertices have no effect on its coboundary."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coefficient-evacuation"), DeclarationHandle.Create(Prefix + "evacuate"),
                H("Evacuation and zero extension"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A(G,e,a) denotes evacuate G e a, whose surviving coordinate f is "
                    + "a(f.val) − a(e) incidence G (target(e)) f.val. J(e,b) denotes extend e b: its e coordinate is zero "
                    + "and each surviving coordinate is b. Both are rational linear maps. The incidence sign is head minus tail."))),
                DescribeRole.Definition),
            Theorem("evacuation-coboundary", "evacuate_coboundary", "Evacuation restricts the vertex potential",
                Context(All("k", Functions(V), Equal(Call("A", G, e, Call("d", G, k)),
                    Call("d", Contract(), Call("restrictVertices", k)))), false, true),
                "On a vertex w, the restricted potential evaluated at vertexMap(w) is k(w) minus "
                + "(k(target(e)) − k(source(e))) times the indicator of w = target(e). Subtracting this identity "
                + "at the two surviving endpoints gives the displayed coboundary transport."),
            Theorem("extension-coboundary", "extend_coboundary", "Zero extension pulls the potential back",
                Context(All("k", Functions(Call("ContractedVertex", G, e)),
                    Equal(Call("J", e, Call("d", Contract(), k)),
                        Call("d", G, Call("compose", k, Call("vertexMap", G, e, h))))), false, true),
                "The endpoints of e have the same image under vertexMap, so the pulled-back coboundary vanishes "
                + "on e. On each surviving edge, the identity is the definition of the contracted endpoint maps."),
            Theorem("evacuation-extension", "evacuate_extend", "One composite is exactly the identity",
                Context(All("b", Functions(Call("Surviving", e)),
                    Equal(Call("A", G, e, Call("J", e, b)), b)), false, false),
                "Zero extension has no deleted coefficient to evacuate; every surviving coordinate is fixed."),
            Theorem("extension-evacuation-correction", "extend_evacuate_sub", "The other composite has an exact coboundary correction",
                Context(All("a", Functions(E), Equal(
                    Seq(Call("J", e, Call("A", G, e, a)), Sp, Minus, Sp, a),
                    Call("d", G, Call("targetCorrection", G, e, a)))), false, true, nonloopBinder: false),
                "targetCorrection(G,e,a)(w) is −a(e) times the indicator of w = target(e). Its coboundary "
                + "is −a(e) at e and −a(e) incidence G (target(e)) f at every surviving edge f. "
                + "Thus J A(a) and a define the same cohomology class."),
            Describe.Lean(DescribeId.Create("quotient-linear-equivalence"), DeclarationHandle.Create(Prefix + "cohomologyEquiv"),
                H("The native quotient linear equivalence"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("cohomologyEquiv G e h, written Psi(G,e,h), is a rational linear equivalence "
                    + "Cohomology G ≃ Cohomology (contract G e h). Mathlib Submodule.mapQ descends A and J using their "
                    + "actual coboundary transport laws. A J = id gives one inverse law, and the target correction "
                    + "gives the other modulo range(coboundary G). No quotient relation or equivalence is assumed."))),
                DescribeRole.Definition),
            Theorem("quotient-representatives", "cohomologyEquiv_representatives", "Both representative computation rules",
                Context(Seq(
                    Grp(All("a", Functions(E), Equal(Call("apply", Psi(), Call("class", G, a)),
                        Call("class", Contract(), Call("A", G, e, a))))), Sp, Land, Sp,
                    Grp(All("b", Functions(Call("Surviving", e)), Equal(
                        Call("inverse", Psi(), Call("class", Contract(), b)), Call("class", G, Call("J", e, b)))))),
                    false, true),
                "Every original representative is evacuated by A; every contracted representative is extended "
                + "by J with zero at the deleted coordinate. These formulas hold on the native quotients without choosing representatives."),
            Theorem("coboundaries-annihilate-cycles", "coboundary_annihilates_cycles", "Finite-endpoint annihilation with arbitrary vertices",
                Context(All("k", Functions(V), All("z", Call("CycleSpace", G),
                    Equal(Call("edgePair", Call("d", G, k), Call("val", z)), D(0)))), true, false, false, false),
                "edgePair(a,z) is the finite sum over edge IDs f of a(f) z(f). Let S be the union of the finite "
                + "source and target images. Interchanging finite sums gives edgePair(d(G,k),z) = "
                + "sum over w in S of k(w) boundary(G,z)(w). Every boundary coordinate vanishes for z in CycleSpace G. "
                + "There is no sum over all vertices and no Fintype V hypothesis."),
            Describe.Lean(DescribeId.Create("quotient-cycle-pairing"), DeclarationHandle.Create(Prefix + "cohomologyPairing"),
                H("Evaluation on the actual cohomology quotient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Mathlib dotProductEquiv identifies edge functions with their coordinate functionals. "
                    + "Restriction to CycleSpace G gives cycleEvaluation G. The annihilation identity permits Submodule.liftQ "
                    + "to define cohomologyPairing G, a rational linear map from Cohomology G to the linear dual of CycleSpace G. "
                    + "Write pairing(G,a,z) for its value. It is independent of the cohomology representative and linear in both entries."))),
                DescribeRole.Definition),
            Theorem("inverse-transpose-naturality", "cohomology_pairing_naturality", "Inverse-transpose coefficient naturality in both directions",
                NaturalityFormula(),
                "Write Phi = cycleEquiv G e h. Its inverse has deleted coefficient "
                + "−residual G e z.val (target(e)), and its surviving coefficients are z. Splitting the edge sum into e "
                + "and the surviving IDs gives edgePair(A(a),z) = edgePair(a,Phi.symm(z)); the deleted term is "
                + "−a(e) residual G e z.val (target(e)). The representative rules and annihilation descend this identity "
                + "to cohomology. Applying it to J(b) and Phi(z) gives the reverse direction. This supplies actual "
                + "coefficient transport for endpoint nonloop contraction. It does not establish perfect duality, cyclic AS signs, "
                + "IHX or CL relation maps, socket gluing, or the complete four-loop Jacobi quotient."))));

    private static readonly Formula V = F.Id("V"), E = F.Id("E"), G = F.Id("G"), e = F.Id("e"),
        h = F.Id("h"), k = F.Id("k"), a = F.Id("a"), b = F.Id("b"), z = F.Id("z");
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula Functions(Formula type) => Seq(Grp(type), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Q"))));
    private static Formula Contract() => Call("contract", G, e, h);
    private static Formula Psi() => Call("Psi", G, e, h);
    private static Formula Context(Formula body, bool finite, bool nonloop, bool selectedEdge = true,
        bool edgeDecidable = true, bool nonloopBinder = true)
    {
        if (nonloop)
        {
            Formula condition = Seq(Call("source", G, e), Sp, Neq, Sp, Call("target", G, e));
            body = nonloopBinder ? All("h", condition, body) : Seq(Grp(condition), Sp, To, Sp, body);
        }
        if (selectedEdge) body = All("e", E, body);
        body = All("G", Call("DirectedMultigraph", V, E), body);
        body = Seq(OpenBracket, Call("DecidableEq", V), CloseBracket, Sp,
            edgeDecidable ? Seq(OpenBracket, Call("DecidableEq", E), CloseBracket, Sp) : Sp,
            finite ? Seq(OpenBracket, Call("Fintype", E), CloseBracket, Comma, Sp, body) : Seq(Comma, Sp, body));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        return Disp(All("V", type, All("E", type, body)));
    }
    private static DocumentBlock Theorem(string id, string name, string title, Formula formula, string explanation) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
    private static Formula NaturalityFormula()
    {
        Formula phi = Call("cycleEquiv", G, e, h);
        Formula rep = All("a", Functions(E), All("z", Call("CycleSpace", G),
            Equal(Call("pairing", G, Call("class", G, a), z), Call("edgePair", a, Call("val", z)))));
        Formula forward = All("a", Call("Cohomology", G), All("z", Call("CycleSpace", Contract()),
            Equal(Call("pairing", Contract(), Call("apply", Psi(), a), z),
                Call("pairing", G, a, Call("inverse", phi, z)))));
        Formula backward = All("b", Call("Cohomology", Contract()), All("z", Call("CycleSpace", G),
            Equal(Call("pairing", G, Call("inverse", Psi(), b), z),
                Call("pairing", Contract(), b, Call("apply", phi, z)))));
        return Context(Seq(Grp(rep), Sp, Land, Sp, Grp(forward), Sp, Land, Sp, Grp(backward)), true, true);
    }
}
