using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class FiniteRectangleTransportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite rectangle menu on the positive five-mode fiber has an exact continuous transport realization.",
        H("Actual Finite Rectangle Transport"),
        Blocks(Describe.Lean(
            DescribeId.Create("finite-rectangles-realize"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiniteRectangleTransport.finite_rectangles_realize"),
            H("Exact realization by finite continuous controls"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The base b is the triple (X,Y,Z), with 0 < Z < 1 and 0 < X,Y < 1-Z. Its open fiber J(b) has endpoints max(0,X+Y-(1-Z)) and min(X,Y). The five probabilities, in the mode order (0,1,2,3,13), are (1-Z-X-Y+k,X-k,Z,Y-k,k). Their strict positivity and total one use the existing InteriorProbability carrier.")),
                Paragraph(Text("The direction is (1,-1,0,-1,1). The information coefficient is the sum of the four reciprocal bottom probabilities. The phase weight w is the direction divided coordinatewise by probability times information. Compatible(q(t)) asserts that the middle phase is zero and that the direction paired with the lifted phases equals the real relation phase. The state of a history q consists of the probability coordinate k, the real lifted relation phase c, and five real lifted phases v. Duration(A) is four times the length of the finite menu A; its phase target is the sum of a times (w(k)-w(k0)) over the entries (k,a).")),
                Paragraph(Text("Admissible(b,N,q) requires continuity of the actual real-time function q, probability coordinates in J(b) on the closed interval from zero to N, finite variation of c, and an affine chart on each unit-time leg. On every open leg and for every mode, the probability derivative equals the direction times the derivative of k, and the derivative of v equals w(k) times the derivative of c. It also requires integrability of every actual transport component and equality of its integral with the corresponding terminal minus initial lifted phase. Thus the supplied object is a piecewise linear control with its transported state lift and exact integral residual.")),
                Paragraph(Text("For each menu entry, the four successive vertices change k from k0 to k, change c from zero to a at k, return k to k0, and return c to zero at k0. The phase changes on the two phase legs are a times w(k) and minus a times w(k0). Concatenating these vertices gives the real-time interpolation; matching endpoints prove continuity, and affine charts give finite variation and the differential law.")),
                Paragraph(Text("All real coefficients, including negative and zero coefficients, repeated heights, either symmetry wall, and the empty menu are included. There is no uniform speed, energy or amplitude bound. This realizes every supplied finite representation; it does not establish the existence of a representation for every vector in the full holonomy space, nor the three-height basis or the compact holonomy group."))),
            DescribeRole.Theorem))));

    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Apply(Formula f, Formula x) => Seq(f, Open, x, Close);
    private static Formula Part(string name, Formula q, Formula t) => Call(name, Apply(q, t));

    private static Formula Statement()
    {
        Formula b = F.Id("b"), e = F.Id("e"), menu = F.Id("A");
        Formula q = F.Id("q"), t = F.Id("t"), p = F.Id("p");
        Formula kzero = Seq(F.Id("k"), Underscore, Grp(D(0)));
        Formula duration = Call("Duration", menu);
        Formula interval = Call("J", b);
        Formula target = Call("residual", Call("phaseWeight", b), kzero, menu);
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, b, Colon, Sp, Operatorname, Grp(F.Id("Base")), Comma, Sp,
            Call("ValidBase", b), Rightarrow, RowBreak, Grp(),
            Forall, Sp, kzero, InMacro, Sp, interval, Comma, Sp,
            Forall, Sp, menu, Colon, Call("List", Seq(R, Caret, Grp(D(2)))), Comma, RowBreak, Grp(),
            Open, Forall, Sp, e, InMacro, Sp, menu, Comma, Sp,
            Call("fst", e), InMacro, Sp, interval, Close, Rightarrow, RowBreak, Grp(),
            Exists, Sp, q, Colon, Seq(R, To, Sp, Operatorname, Grp(F.Id("State"))), Comma, Sp,
            Call("Admissible", b, duration, q), Land, RowBreak, Grp(),
            Apply(q, D(0)), Eq, Open, kzero, Comma, D(0), Comma, D(0), Close, Land, RowBreak, Grp(),
            Part("kappa", q, duration), Eq, kzero, Land, Sp,
            Part("chi", q, duration), Eq, D(0), Land, RowBreak, Grp(),
            Open, Forall, Sp, t, InMacro, Sp, OpenBracket, D(0), Comma, duration, CloseBracket,
            Comma, Sp, Exists, Sp, p, Colon, Call("InteriorProbability", D(4)), Comma, Sp,
            Call("weight", p), Eq, Call("probability", b, Part("kappa", q, t)), Close,
            Land, RowBreak, Grp(),
            Open, Forall, Sp, t, InMacro, Sp, OpenBracket, D(0), Comma, duration, CloseBracket,
            Comma, Sp, Call("Compatible", Apply(q, t)), Close, Land, RowBreak, Grp(),
            Part("phase", q, duration), Eq, target,
            End, Grp(F.Id("gathered"))));
    }
}
