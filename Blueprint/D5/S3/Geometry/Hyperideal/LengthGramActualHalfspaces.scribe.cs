using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Hyperideal;

internal sealed class LengthGramActualHalfspacesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Eight actual halfspaces and their facets for the same six-length radial map.",
        H("The supplied length frame and radial map"),
        Blocks(
            Paragraph(Text("Rsix and Rfour denote real six- and four-coordinate spaces, "
                + "Matrixfour denotes real four-by-four matrices, and Hthree and Htwo "
                + "denote HyperbolicThreeSpace and UpperHalfPlane with their actual "
                + "hyperbolic metrics and topologies. The six entries of l retain the "
                + "order (01,02,03,23,13,12). Put G(l)=lengthGram(l): its diagonal is "
                + "one, and G01=-cosh(l0), G02=-cosh(l1), G03=-cosh(l2), "
                + "G23=-cosh(l3), G13=-cosh(l4), G12=-cosh(l5), with symmetry. "
                + "C(l) is the same cutBody: v has nonnegative coordinates summing "
                + "to one and every row of G(l) evaluated on v is nonpositive. "
                + "Write q(l,v)=v-transpose G(l) v, r(l,v)=v/sqrt(-q(l,v)), "
                + "and b=(1/4,1/4,1/4,1/4). A member of C(l) below is the subtype "
                + "element, and Val takes its underlying Rfour vector.")),
            Paragraph(Text("B is the Lorentz form with signs (+,+,+,-), Phi is the "
                + "original LengthGramMetricSegments.lift, Row(M,i) is row i of the "
                + "supplied M, and Vecmul denotes row-vector matrix multiplication. "
                + "For future unit timelike y, Psi(y) is the upper-half-space "
                + "coordinate pair ((y0+i*y1)/(y3-y2),1/(y3-y2)), expressed through "
                + "WithLp.toLp 2. Coordinates is the actual coordinate value of an "
                + "Hthree point. The displayed existential coordinate condition "
                + "requires this equation for the same supplied f at every v in C(l). "
                + "It includes B(y,y)=-1 and y3>0.")),
            Paragraph(Text("Let T be (Fin 4)+(Fin 4), the eight coefficient supports. "
                + "For a=inl(i), S(l,a,v)=-v_i; for a=inr(i), "
                + "S(l,a,v)=sum_j G(l)_ij*v_j. Put Dual(l,M,i)=Row(inverse(G(l)),i)*M, "
                + "w(l,inl(i))=sqrt(inverse(G(l))_ii), and w(l,inr(i))=1. "
                + "The outward normals are A(l,M,inl(i))=-Dual(l,M,i)/w(l,inl(i)) "
                + "and A(l,M,inr(i))=Row(M,i). For p in Hthree write "
                + "V(l,M,a,p)=B(Phi(p),A(l,M,a)). Define K(l,M) by all eight "
                + "inequalities V<=0 and Strict(l,M) by all eight inequalities V<0. "
                + "These normals use the supplied rows and their Gram duals.")),
            Describe.Lean(
                DescribeId.Create("same-image-halfspaces"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/LengthGramActualHalfspaces.same_image_halfspaces"),
                H("Closed halfspaces reconstruct the same image"),
                StatementSource.FromAuthor(F.Disp(ImageStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Assume all six l entries are positive, the Lorentz "
                        + "Gram of M is G(l), det(M)>0, det(G(l))<0, and f satisfies "
                        + "the displayed future radial-coordinate condition. Then "
                        + "Range(f)=K(l,M), including every equality boundary. This "
                        + "statement has no additional source-cosine, continuity, "
                        + "injectivity, compactness or nonemptiness hypothesis.")),
                    Paragraph(Text("The frame identities give B(x*M,Dual(l,M,i))=x_i "
                        + "and B(x*M,Row(M,i))=(G(l)*x)_i. Diagonal cofactors are "
                        + "negative because each adjacent hyperbolic cosine exceeds "
                        + "one; division by det(G(l))<0 makes each inverse diagonal "
                        + "positive. Thus all w are positive, and for v in C(l) "
                        + "V(l,M,a,f(v))=S(l,a,Val(v))/(sqrt(-q(l,Val(v)))*w(l,a)). "
                        + "Every point of Range(f) satisfies the eight closed signs.")),
                    Paragraph(Text("Conversely, for p satisfying the closed signs, "
                        + "set x=Phi(p)*inverse(M). The dual signs give x_i>=0 and "
                        + "the cap signs give (G(l)*x)_i<=0. The unit lift equation "
                        + "gives q(l,x)=-1, hence s=sum_i x_i>0. The vector v=x/s "
                        + "lies in the same C(l), and sqrt(-q(l,v))=1/s, so r(l,v)=x. "
                        + "The supplied coordinate condition gives Phi(f(v))=Phi(p). "
                        + "Injectivity of Phi then gives f(v)=p. The argument recovers "
                        + "a preimage under the original f at closed as well as strict signs."))),
                DescribeRole.Theorem),
            Paragraph(Text("For the remaining statement, phi(l) is exactly "
                + "FourCycleEnvelopes.cosine(cosh(l0),cosh(l1),cosh(l2),cosh(l3), "
                + "cosh(l4),cosh(l5)). Only this one source cosine is required to "
                + "lie between -1 and 1. Delta(i,j) is one if i=j and zero otherwise. "
                + "Invdiag(l,i) and Inventry(l,i,j) are the corresponding entries "
                + "of inverse(G(l)), and Gentry(l,i,j)=G(l)_ij. Entry is coordinate "
                + "evaluation, Apply is map evaluation, Maps and Sets denote function "
                + "and set types, and A(l,M) denotes the whole normal function on T.")),
            Paragraph(Text("Oriented(l,M) is the set of p with, for every i, "
                + "B(Phi(p),Dual(l,M,i))>=0 and B(Phi(p),Row(M,i))<=0. "
                + "Orientedstrict(l,M) uses >0 and <0 respectively. H(l,M,a) is "
                + "{p:V(l,M,a,p)<=0}, Plane(l,M,a) is {p:V(l,M,a,p)=0}, and "
                + "Active(l,M,f) is {p in Range(f):there exists a in T with "
                + "V(l,M,a,p)=0}. Coeffacet(l,a) is {v in C(l):S(l,a,Val(v))=0}; "
                + "Facet(l,M,f,a) is {p in Range(f):V(l,M,a,p)=0}. "
                + "Deleted(l,M,a) is {p:for every b in T different from a, "
                + "V(l,M,b,p)<=0}. Image denotes the image of the stated set under "
                + "the stated map. Interior and Frontier act in the whole Hthree "
                + "topology on Hthree sets. Open(U) below acts in Htwo.")),
            Paragraph(Text("Put c_i=sum_(j different from i) -G(l)_ij. The explicit "
                + "vector W(l,inl(i)) has entry zero at i and 1/3 elsewhere. "
                + "W(l,inr(i)) has entry c_i/(c_i+3) at i and 1/(c_i+3) elsewhere. "
                + "These are exactly facetWitness. Their selected support vanishes "
                + "and all seven other coefficient supports are strictly negative. "
                + "Positive lengths give c_i>3, so the cap denominators are positive.")),
            Describe.Lean(
                DescribeId.Create("same-supplied-actual-halfspaces"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Hyperideal/LengthGramActualHalfspaces.same_supplied_actual_halfspaces"),
                H("Actual interiors, complete support planes and irredundant facets"),
                StatementSource.FromAuthor(F.Disp(SuppliedStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Retain the same arbitrary six positive lengths, "
                        + "one-cosine admissibility, supplied M, both determinant "
                        + "inequalities and supplied future radial-coordinate f. "
                        + "The statement also retains continuity and injectivity of f "
                        + "and compactness and nonemptiness of its range. These are "
                        + "the original assumptions even where a smaller argument "
                        + "uses fewer of them. The formula lists all twenty conclusions.")),
                    Paragraph(Text("Congruence G(l)=M*diag(1,1,1,-1)*transpose(M) gives "
                        + "det(G(l))=-det(M)^2. Inverting G gives the displayed "
                        + "dual-row and dual-dual pairings; positive inverse diagonal "
                        + "then gives B(A(a),A(a))=1 for each of the eight outward normals. "
                        + "The image reconstruction yields both closed sign descriptions. "
                        + "The barycenter has every support strict, and its same f-image "
                        + "therefore lies in the ambient interior.")),
                    Paragraph(Text("For any active support at p, the actual global "
                        + "metric-line result with tangent A(a) gives an isometry g "
                        + "from the real line with g(0)=p and "
                        + "Phi(g(t))=cosh(t)*Phi(p)+sinh(t)*A(a). Its selected readout "
                        + "is sinh(t). Every positive t violates the support, arbitrarily "
                        + "close to p. Thus an active equality excludes ambient interior. "
                        + "Finitely many continuous strict signs form an open set, and "
                        + "the weak signs form a closed set. This gives both interior "
                        + "descriptions and the entire ambient frontier.")),
                    Paragraph(Text("Each unit spacelike normal has a complete Htwo "
                        + "isometric realization with range Plane(l,M,a). The same "
                        + "crossing argument identifies that plane as the full frontier "
                        + "of its single halfspace H(l,M,a). The positive readout "
                        + "denominator identifies the image of each coefficient facet "
                        + "with exactly Facet(l,M,f,a). The point f(W(l,a)) has only "
                        + "the selected equality; the other seven signs remain strict.")),
                    Paragraph(Text("Pulling the other seven strict signs back along "
                        + "the complete plane isometry gives a nonempty open U in Htwo "
                        + "whose image lies in the same coefficient facet image. "
                        + "Along the transverse g, all seven signs remain strict for "
                        + "sufficiently small positive t, while the selected sign is "
                        + "positive. This supplies each strict deletion point and proves "
                        + "Range(f) is a proper subset of Deleted(l,M,a). If two "
                        + "outward normals coincided, the selected equality at an "
                        + "isolated facet point would contradict the other strict sign. "
                        + "Hence the outward-normal function is injective.")),
                    Paragraph(Text("Application: the shared_radial_body construction, "
                        + "under its one strict source-cosine condition, provides M "
                        + "and f satisfying this full telescope for the same l. "
                        + "Applying the two results to those supplied objects identifies "
                        + "that body's actual eight-halfspace image and its ambient "
                        + "facets. An inverse strict-angle construction may be used "
                        + "only after its lengths and this same frame/map contract "
                        + "have been established. The formulas make no identification "
                        + "of source-angle readouts with all actual dihedral angles.")),
                    Paragraph(Text("The conclusions give complete supporting Htwo "
                        + "planes and open facet patches. They do not give the complete "
                        + "cyclic triangular/hexagonal incidence, actual all-dihedral "
                        + "data, edge stars, charts, all-orbit quotient bridges, "
                        + "Schlaefli or volume formulas, global CFMP, or a metric "
                        + "identity from this native body to a current cyclic sector. "
                        + "Lower bounds and abstract metric constructions do not "
                        + "supply these remaining geometric identifications. The "
                        + "Lorentz constructions are classical; no novelty claim is made."))),
                DescribeRole.Theorem))));

    private static Formula ImageStatement()
    {
        var l = F.Id("l"); var m = F.Id("M"); var f = F.Id("f");
        return All("l", F.Id("Rsix"), All("M", F.Id("Matrixfour"),
            All("f", Call("Maps", Call("C", l), F.Id("Hthree")),
                Implies(And(Frame(l, m, f), Positive(l), Gram(l, m),
                    Lt(F.D(0), Call("Det", m)), Lt(Call("Det", Call("G", l)), F.D(0))),
                    Eq(Call("Range", f), Call("K", l, m))))));
    }

    private static Formula SuppliedStatement()
    {
        var l = F.Id("l"); var m = F.Id("M"); var f = F.Id("f");
        return All("l", F.Id("Rsix"), Implies(Positive(l),
            Implies(And(Lt(new Formula.Negate(F.D(1)), Call("phi", l)),
                Lt(Call("phi", l), F.D(1))),
                All("M", F.Id("Matrixfour"), Implies(And(Gram(l, m),
                    Lt(F.D(0), Call("Det", m)), Lt(Call("Det", Call("G", l)), F.D(0))),
                    All("f", Call("Maps", Call("C", l), F.Id("Hthree")),
                        Implies(And(Call("Continuous", f), Call("Injective", f),
                            Call("IsCompact", Call("Range", f)),
                            Call("Nonempty", Call("Range", f)), Frame(l, m, f)),
                            Conclusions(l, m, f))))))));
    }

    private static Formula Positive(Formula l) =>
        All("k", Call("Fin", F.D(6)), Lt(F.D(0), Call("Entry", l, F.Id("k"))));

    private static Formula Gram(Formula l, Formula m) =>
        All("i", Call("Fin", F.D(4)), All("j", Call("Fin", F.D(4)),
            Eq(Call("B", Call("Row", m, F.Id("i")), Call("Row", m, F.Id("j"))),
                Call("Gentry", l, F.Id("i"), F.Id("j")))));

    private static Formula Frame(Formula l, Formula m, Formula f)
    {
        var v = F.Id("v"); var y = F.Id("y");
        return All("v", Call("C", l), Exists("y", F.Id("Rfour"), And(
            Eq(y, Call("Vecmul", Call("r", l, Call("Val", v)), m)),
            Eq(Call("B", y, y), new Formula.Negate(F.D(1))),
            Lt(F.D(0), Call("Entry", y, F.D(3))),
            Eq(Call("Coordinates", Call("Apply", f, v)), Call("Psi", y)))));
    }

    private static Formula Conclusions(Formula l, Formula m, Formula f)
    {
        var i = F.Id("i"); var j = F.Id("j"); var a = F.Id("a");
        var c = Call("C", l); var range = Call("Range", f);
        var interior = Call("Interior", range); var k = Call("K", l, m);
        return And(
            Eq(Call("Det", Call("G", l)),
                new Formula.Negate(new Formula.Power(Call("Det", m), F.D(2)))),
            All("i", Call("Fin", F.D(4)), Lt(F.D(0), Call("Invdiag", l, i))),
            All("i", Call("Fin", F.D(4)), All("j", Call("Fin", F.D(4)),
                Eq(Call("B", Call("Dual", l, m, i), Call("Row", m, j)), Call("Delta", i, j)))),
            All("i", Call("Fin", F.D(4)), All("j", Call("Fin", F.D(4)),
                Eq(Call("B", Call("Dual", l, m, i), Call("Dual", l, m, j)),
                    Call("Inventry", l, i, j)))),
            All("a", F.Id("T"), Eq(Call("B", Call("A", l, m, a), Call("A", l, m, a)), F.D(1))),
            Eq(range, k),
            Eq(range, Call("Oriented", l, m)),
            Eq(interior, Call("Strict", l, m)),
            Eq(interior, Call("Orientedstrict", l, m)),
            In(Call("Apply", f, F.Id("b")), interior),
            Call("Nonempty", interior),
            Call("IsClosed", range),
            Eq(Call("Frontier", range), Call("Active", l, m, f)),
            All("a", F.Id("T"), CompletePlane(l, m, a)),
            All("a", F.Id("T"), Eq(Call("Image", f, Call("Coeffacet", l, a)),
                Call("Facet", l, m, f, a))),
            All("a", F.Id("T"), Exists("v", c, And(
                Eq(Call("Val", F.Id("v")), Call("W", l, a)),
                Eq(Value(l, m, a, Call("Apply", f, F.Id("v"))), F.D(0)),
                OtherStrict(l, m, a, Call("Apply", f, F.Id("v")))))),
            All("a", F.Id("T"), Patch(l, m, f, a)),
            All("a", F.Id("T"), Exists("p", F.Id("Hthree"), And(
                Lt(F.D(0), Value(l, m, a, F.Id("p"))), OtherStrict(l, m, a, F.Id("p"))))),
            All("a", F.Id("T"), And(Subset(range, Call("Deleted", l, m, a)),
                Ne(range, Call("Deleted", l, m, a)))),
            Call("Injective", Call("A", l, m)));
    }

    private static Formula CompletePlane(Formula l, Formula m, Formula a)
    {
        var e = F.Id("e"); var h = Call("H", l, m, a);
        return And(Call("IsClosed", h),
            Exists("e", Call("Maps", F.Id("Htwo"), F.Id("Hthree")), And(
                Call("Isometry", e), Eq(Call("Range", e), Call("Plane", l, m, a)),
                Eq(Call("Frontier", h), Call("Range", e)))));
    }

    private static Formula Patch(Formula l, Formula m, Formula f, Formula a)
    {
        var e = F.Id("e"); var u = F.Id("U");
        return Exists("e", Call("Maps", F.Id("Htwo"), F.Id("Hthree")),
            Exists("U", Call("Sets", F.Id("Htwo")), And(
                Call("Isometry", e), Eq(Call("Range", e), Call("Plane", l, m, a)),
                Call("Open", u), Call("Nonempty", u),
                Subset(Call("Image", e, u), Call("Image", f, Call("Coeffacet", l, a))))));
    }

    private static Formula OtherStrict(Formula l, Formula m, Formula a, Formula p) =>
        All("b", F.Id("T"), Implies(Ne(F.Id("b"), a), Lt(Value(l, m, F.Id("b"), p), F.D(0))));
    private static Formula Value(Formula l, Formula m, Formula a, Formula p) => Call("V", l, m, a, p);
    private static Formula All(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula Exists(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), d, b);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(F.Id(n), [.. a]);
    private static Formula And(params Formula[] a)
    {
        var result = a[^1];
        for (var i = a.Length - 2; i >= 0; i--)
            result = new Formula.Logic(a[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Subset(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.SubsetOf, b);
}
