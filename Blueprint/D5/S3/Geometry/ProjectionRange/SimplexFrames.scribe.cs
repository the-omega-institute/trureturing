using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ProjectionRange;

internal sealed class SimplexFramesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous range frames over singular simplices",
        H("Continuous range frames over singular simplices"),
        Blocks(
            Paragraph(Text("SimplexProjectionData in the formula consists of an arbitrary type B with a TopologicalSpace instance; arbitrary natural numbers n,r,k; a map P:B -> Matrix (Fin n) (Fin n) C; continuity of P; the pointwise equations P(b)*=P(b) and P(b)P(b)=P(b); the pointwise rank equation rank(P(b))=r; a proof k<=3; and a continuous singular simplex sigma:C(SimplexCategory.toTop.obj [k],B). The star means conjugate transpose. All these data, including the dimension bound and sigma, are quantified together as q. No topology on B beyond the given topology is required.")),
            Paragraph(Text("Write X(q)=SimplexCategory.toTop.obj [k], the original ULift of StdSimplex R (Fin (k+1)), and V(m)=EuclideanSpace C (Fin m). Indices(q) is Fin r. Columns(q) is Fin r -> C(X(q),V(n)); Coordinates(q) is C(X(q),V(n) ->L[C] V(r)). Range(q,x) is the actual complex linear range of Matrix.toEuclideanLin(P(sigma(x))) in V(n), and Fiber(q,x) is that range as a subtype. Column(q,s,x,i)=s(i)(x), Coordinate(q,a,x,v)=a(x)(v), and Basis(q,i)=EuclideanSpace.single i (1:C). Ambient(q,v) is the underlying V(n) vector of a fiber element. Reconstruct(q,s,a,x,v) is the finite sum over i:Fin r of (a(x)(Ambient(q,v)))(i) times s(i)(x). Multiplication of a vector by that complex coordinate means scalar multiplication.")),
            Describe.Lean(
                DescribeId.Create("simplexframes"),
                DeclarationHandle.Create("D5/S3/Geometry/ProjectionRange/SimplexFrames.range_projection_simplex_frames"),
                H("range_projection_simplex_frames"),
                StatementSource.FromAuthor(FrameFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There are continuous ambient columns s and continuous ambient complex-linear coordinates a. For every x and i the column belongs to the actual projection range and has coordinate vector e_i. For every actual fiber vector v, the coordinate-weighted sum of these columns is v in the ambient Euclidean space. The coordinates are defined on the whole ambient space, while the reconstruction identity is asserted for vectors in the actual range.")),
                    Paragraph(Text("Choose the vertex v0 given by the zeroth element of Fin(k+1). On the original ULift simplex define H(t,x) by lifting the convex combination (1-t)v0+t x. Its weights are continuous in t and x, so H is continuous, H(0,x)=v0 and H(1,x)=x. The simplex is compact, including when k=0. This constructs the contraction of the actual singular-simplex domain.")),
                    Paragraph(Text("Set E=V(n) ->L[C] V(n). Transport P along sigma and H, then convert each matrix to its continuous linear operator. This gives Q(t,x)=matrixCLE(P(sigma(H(t,x)))). Currying gives a continuous map F:[0,1] -> C(X,E). The compactness of X and completeness of E give the complete normed-ring structure on C(X,E). Matrix multiplication corresponds to operator composition, so F(t)^2=F(t) pointwise. Apply connected_idempotents_intertwiner at 0 and 1 in this map ring.")),
                    Paragraph(Text("Let U be the continuous operator-valued map supplied by the resulting unit and W its inverse. Evaluation gives P_x U_x=U_x P_0, U_x W_x=I and W_x U_x=I, where P_x denotes the operator of P(sigma(x)) and P_0 that of P(sigma(v0)). These are identities across the entire simplex. In particular U_x is injective.")),
                    Paragraph(Text("At b0=sigma(v0), use the existing actual-range column chart. Let A0:V(r) ->L[C] V(n) be its selected-column operator and C0:V(n) ->L[C] V(r) its inverse-Gram coordinate operator. The chart gives A0(z) in Ran P_0, C0 A0=I, and A0 C0(v)=v for v in Ran P_0. Hermitian idempotence and constant rank provide this chart; no frame is an input.")),
                    Paragraph(Text("Define s_i(x)=U_x A0(e_i) and a(x)=C0 W_x. Evaluation and composition of continuous operator maps prove their continuity. Because P_x U_x=U_x P_0 and P_0 A0(e_i)=A0(e_i), each s_i(x) is fixed by P_x. Idempotence identifies this fixed-vector condition with actual range membership. The inverse identity W_x U_x=I and C0 A0=I give a(x)(s_i(x))=e_i.")),
                    Paragraph(Text("For an actual range vector v at x, the equation P_x v=v and the intertwining identity imply U_x P_0 W_x v=v=U_x W_x v. Injectivity of U_x gives P_0 W_x v=W_x v, hence W_x v is in Ran P_0. Put z=C0 W_x v. Expand z as the sum of z_i e_i, apply the linear maps A0 and U_x to that sum, and use A0 C0 W_x v=W_x v. The resulting sum is U_x W_x v=v, which proves exactly the ambient reconstruction conjunct.")),
                    Paragraph(Text("The parameters n and r may be zero. The same operator identities and the empty Fin r sum apply; no positive-rank or positive-dimension step is used. The vertex exists also for k=0. The bound k<=3 remains part of the statement. An empty B is permitted by the quantified data, although then a singular simplex into B cannot be supplied. Compactness is used for X and the continuous-map algebra, not imposed on B.")),
                    Paragraph(Text("This is the standard contraction-and-transport construction for projection ranges. It uses the existing column-chart and inverse-Gram identities, the idempotent transport theorem, and Mathlib's genuine topological simplex, compact simplex, compact-open currying and continuous-map normed-ring structures. These sources support the argument and its implementation; no claim of literature novelty is made."))),
                DescribeRole.Theorem)),
        []));

    private static Formula FrameFormula()
    {
        Formula q = F.Id("q"), s = F.Id("s"), a = F.Id("a"), x = F.Id("x"), i = F.Id("i"), v = F.Id("v");
        Formula membership = F.Grp(F.Open, F.Forall, F.Sp, x, F.InMacro, F.Sp, Call("X", q), F.Comma, F.Sp,
            F.Forall, F.Sp, i, F.InMacro, F.Sp, Call("Indices", q), F.Comma, F.Sp,
            Call("Column", q, s, x, i), F.InMacro, F.Sp, Call("Range", q, x), F.Close);
        Formula coordinates = F.Grp(F.Open, F.Forall, F.Sp, x, F.InMacro, F.Sp, Call("X", q), F.Comma, F.Sp,
            F.Forall, F.Sp, i, F.InMacro, F.Sp, Call("Indices", q), F.Comma, F.Sp,
            Call("Coordinate", q, a, x, Call("Column", q, s, x, i)), F.Sp, F.Eq, F.Sp, Call("Basis", q, i), F.Close);
        Formula reconstruction = F.Grp(F.Open, F.Forall, F.Sp, x, F.InMacro, F.Sp, Call("X", q), F.Comma, F.Sp,
            F.Forall, F.Sp, v, F.InMacro, F.Sp, Call("Fiber", q, x), F.Comma, F.Sp,
            Call("Reconstruct", q, s, a, x, v), F.Sp, F.Eq, F.Sp, Call("Ambient", q, v), F.Close);
        return F.Disp(F.Seq(
            F.Forall, F.Sp, q, F.InMacro, F.Sp, F.Id("SimplexProjectionData"), F.Comma, F.Sp,
            F.Exists, F.Sp, s, F.InMacro, F.Sp, Call("Columns", q), F.Comma, F.Sp,
            F.Exists, F.Sp, a, F.InMacro, F.Sp, Call("Coordinates", q), F.Comma, F.Sp,
            F.Grp(membership, F.Sp, F.Land, F.Sp, coordinates, F.Sp, F.Land, F.Sp, reconstruction), F.Dot));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
}
