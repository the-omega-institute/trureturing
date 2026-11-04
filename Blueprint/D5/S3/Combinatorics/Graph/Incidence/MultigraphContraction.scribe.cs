using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Incidence;

internal sealed class MultigraphContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Incidence/MultigraphContraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonloop contraction of an edge-indexed directed multigraph preserves rational signed-incidence cycles by surviving-coordinate restriction.",
        H("Multigraph Contraction on Rational Cycles"),
        Blocks(
            Paragraph(Text("Let G be EssentialWordRealization.DirectedMultigraph V E. "
                + "E is finite, while V may be arbitrary. Distinct edge IDs remain distinct even when their endpoints agree. "
                + "No connectedness, simplicity, cyclic vertex order, or condition on bridges is imposed.")),
            Describe.Lean(DescribeId.Create("actual-signed-boundary"),
                DeclarationHandle.Create(Prefix + "boundary"), H("The actual rational boundary"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("incidence G v f is the rational cast of the existing integer "
                    + "signedIncidence G.source G.target v f. Its sign is head minus tail. "
                    + "boundary G is multiplication by this matrix on E-indexed rational coefficients; "
                    + "CycleSpace G is its kernel. Every loop has zero boundary, including loops retained after contraction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("endpoint-contraction"),
                DeclarationHandle.Create(Prefix + "contract"), H("Delete one edge and identify its endpoints"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For e with source(e) different from target(e), Surviving e is the subtype "
                    + "of original edge IDs f different from e. ContractedVertex G e is the subtype of vertices different "
                    + "from target(e). vertexMap sends target(e) to source(e) and fixes every other vertex. "
                    + "contract G e h has the same existing DirectedMultigraph structure with source and target "
                    + "obtained by composing the original endpoint maps with vertexMap. All isolated vertices other "
                    + "than the removed endpoint persist. Parallel edges retain their IDs, and an edge joining the "
                    + "identified vertices becomes a loop rather than disappearing."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonloop-contraction-cycle-equivalence"),
                DeclarationHandle.Create(Prefix + "nonloop_contraction_cycle_equiv"),
                H("Endpoint fibers and the cycle equivalence"),
                StatementSource.FromAuthor(ContractionFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the formula, coeff(z,f) means the underlying cycle coefficient z.val f; "
                        + "inverse(Phi,z) means Phi.symm z. LinearEquiv(Q,A,B) denotes a Q-linear equivalence. "
                        + "The fiber identity identifies precisely the two selected endpoints and no other vertices. "
                        + "The forward equivalence literally restricts surviving coordinates. Its inverse preserves "
                        + "each surviving coefficient and reconstructs the deleted coefficient as the negative "
                        + "original target-row residual. residual G e x v is the sum, over surviving IDs f, "
                        + "of incidence G v f times x(f).")),
                    Paragraph(Text("The contracted boundary at a vertex other than the merged source is its original "
                        + "surviving-edge boundary. At the merged source it is the sum of the original source "
                        + "and target residuals. On a full cycle the removed edge contributes minus its coefficient "
                        + "at the source and plus its coefficient at the target, so restriction has zero contracted "
                        + "boundary. Conversely the target balance fixes the removed coefficient, and the merged "
                        + "balance then proves the source balance. These identities prove both inverse laws. "
                        + "The argument includes bridges, loops, parallel edges, empty surviving edge types, "
                        + "and arbitrary additional isolated vertices.")),
                    Paragraph(Text("This supplies the cycle-space transport step in the common-contraction argument "
                        + "of the caller-supplied completed marked-four-loop proof, Section Half-edge rule and the "
                        + "homology calculation, proof.tex SHA256 "
                        + "7723959228b1445082f506550b1473155eb8210a27f8025e7a56d1a669663d82. "
                        + "The primary mathematical source is Kuperberg, arXiv:2608.11334v1, oddvas.tex. "
                        + "Cyclic-order signs, actual AS/IHX/CL relation maps, cohomology, coefficient duality, "
                        + "socket gluing, and the marked odd two-color four-loop Jacobi quotient require further arguments."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);

    private static Formula ContractionFormula()
    {
        Formula V = F.Id("V"), E = F.Id("E"), G = F.Id("G"), e = F.Id("e");
        Formula h = F.Id("h"), w = F.Id("w"), v = F.Id("v"), z = F.Id("z"), f = F.Id("f");
        Formula phi = F.Id("Phi"), q = Seq(Mathbb, Grp(F.Id("Q")));
        Formula universe = Seq(Operatorname, Grp(F.Id("Type")));
        Formula a = Call("source", G, e), b = Call("target", G, e);
        Formula c = Call("contract", G, e, h), cv = Call("ContractedVertex", G, e);
        Formula se = Call("Surviving", e), cg = Call("CycleSpace", G), cc = Call("CycleSpace", c);
        Formula fiber = All("w", V, All("v", cv,
            Seq(Equal(Call("vertexMap", G, e, h, w), v), Sp, Iff, Sp,
                Equal(w, Call("val", v)), Sp, Lor, Sp,
                Grp(Seq(Equal(w, b), Sp, Land, Sp, Equal(Call("val", v), a))))));
        Formula forward = All("z", cg, All("f", se,
            Equal(Call("coeff", Call("apply", phi, z), f), Call("coeff", z, Call("val", f)))));
        Formula removed = All("z", cc,
            Equal(Call("coeff", Call("inverse", phi, z), e),
                Seq(Minus, Call("residual", G, e, Call("val", z), b))));
        Formula surviving = All("z", cc, All("f", se,
            Equal(Call("coeff", Call("inverse", phi, z), Call("val", f)), Call("coeff", z, f))));
        Formula body = Seq(Grp(fiber), Sp, Land, Sp, Exists, Sp, phi, Colon, Sp,
            Call("LinearEquiv", q, cg, cc), Comma, Sp,
            Grp(forward), Sp, Land, Sp, Grp(removed), Sp, Land, Sp, Grp(surviving));
        Formula assumptions = Seq(OpenBracket, Call("DecidableEq", V), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", E), CloseBracket, Sp,
            OpenBracket, Call("Fintype", E), CloseBracket, Comma, Sp,
            All("G", Call("DirectedMultigraph", V, E), All("e", E,
                All("h", Seq(a, Sp, Neq, Sp, b), body))));
        return Disp(All("V", universe, All("E", universe, assumptions)));
    }
}
