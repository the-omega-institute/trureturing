using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class FiniteZeroGuardedClosureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Zero-guarded coordinate permutations have uniform transport conditions and a closed generated relation.",
        H("Finite zero-guarded permutation identifications"),
        Blocks(
            Paragraph(Text("Let T and I be arbitrary finite types. Give T a discrete "
                + "topology, and let A be any Hausdorff topological space with a "
                + "designated element zero. Let S be any subset of the coordinate "
                + "space of maps from I to A, with its relative product topology. "
                + "Assume S is invariant under every coordinate permutation: if z "
                + "belongs to S, then reindex(rho,z), whose i-th coordinate is "
                + "z(rho inverse(i)), also belongs to S. The types T and I and the "
                + "set S may be empty. Neither closedness nor compactness of S is required.")),
            Paragraph(Text("For each pair (t,f) in T times I, fix an arbitrary target "
                + "label next(t,f) and an arbitrary permutation sigma(t,f) of I. "
                + "These data depend only on the label and coordinate index. "
                + "Write K for the subtype of S and permute(rho,z) for reindex(rho,z) "
                + "viewed as a point of K, using the invariance assumption. "
                + "Set X=T times K. A generating identification seam(a,b) holds "
                + "precisely when some coordinate f of a's carrier point is zero "
                + "and b=(next(a's label,f),permute(sigma(a's label,f),a's carrier point)). "
                + "Let R be the equivalence closure of this exact generating relation.")),
            Paragraph(Text("For a finite subset Z of I, zeroOn(z,Z) means that every "
                + "coordinate indexed by Z is zero. Define guard(t,u,rho,Z) to mean "
                + "that R relates (t,z) to (u,permute(rho,z)) for every z in K "
                + "satisfying zeroOn(z,Z). This is a uniform assertion about the "
                + "generated relation, not an additional hypothesis. "
                + "The finite state type is State=T times T times Perm(I) times Finsets(I), "
                + "with the factors associated to the right. Here coord evaluates "
                + "the underlying coordinate of a subtype point; fst and snd are "
                + "product projections. Types denotes the universe of types, Maps "
                + "a function type, Sets a powerset, Subtype the subtype of a set, "
                + "and card the finite cardinality. In the displayed formula, seam and guard explicitly receive T,I,A,S,next,sigma; their definitions are the ones above. relationSet(R) is the set of "
                + "pairs related by R, and indexedUnion(pieces,State) is the union "
                + "of the State-indexed sets.")),
            Describe.Lean(
                DescribeId.Create("uniform-zero-guarded-closed-relation"),
                DeclarationHandle.Create(
                    "D5/S3/Geometry/Gluing/FiniteZeroGuardedClosure.uniform_transport_and_closed_relation"),
                H("Uniform transport, finite closed pieces and exact state count"),
                StatementSource.FromAuthor(F.Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Induct on the equivalence closure while retaining "
                        + "both a cumulative permutation and a finite set of source "
                        + "coordinates that must be zero. A generating identification "
                        + "uses its supplied permutation and the singleton guard. "
                        + "Reflexivity uses the identity permutation and the empty guard. "
                        + "For symmetry, invert the cumulative permutation and send "
                        + "the guard set through the original permutation. The original "
                        + "uniform assertion then applies to the inverse-permuted point. "
                        + "For transitivity, multiply the two permutations and take "
                        + "the union of the first guard with the second guard pulled "
                        + "back through the first permutation. Both segments are then "
                        + "valid at the same source point and its actual intermediate image.")),
                    Paragraph(Text("Consequently every related pair has one uniform "
                        + "guarded transport description, and applying a guard to the "
                        + "actual source point proves the converse. For each state "
                        + "(t,u,rho,Z), take the set of pairs whose labels are t,u, "
                        + "whose source satisfies zeroOn(z,Z), and whose target carrier "
                        + "is permute(rho,z), provided guard(t,u,rho,Z) holds; otherwise "
                        + "take the empty set. These are the closed pieces in the theorem. "
                        + "The graph condition is closed because the permutation is "
                        + "continuous and K is Hausdorff. The coordinate-zero conditions "
                        + "are closed, and the label conditions are closed in discrete T. "
                        + "Their intersection is therefore closed in X times X.")),
                    Paragraph(Text("The uniform equivalence identifies R exactly with "
                        + "the union of these pieces. The four finite factors give "
                        + "card(State)=card(T) squared times factorial(card(I)) times "
                        + "two to the power card(I). A finite union of closed sets is "
                        + "closed. This closedness is relative to the original subtype "
                        + "carrier and its product topology; no closedness of S in the "
                        + "ambient coordinate space is inferred or needed. "
                        + "No inverse pairing, freeness, nonempty carrier, algebraic "
                        + "operations on A, or manifold structure is assumed.")),
                    Paragraph(Text("Application to the original retained tetrahedra. Let G be any group acting on the right on a finite discrete set Omega, with arbitrary u and v. Use T=Omega, I=Fin(4), A=Real and the actual TruncatedTetrahedron carrier from ActualLinkAffineFan: every coordinate lies between zero and three quarters and their sum is one. All coordinate permutations preserve this carrier. Set next(t,f)=act(t,faceWord(u,v,f)) and sigma(t,f)=facePerm(f), using the original four whole-face permutations and both inverse words. The theorem's seam is literally TruncatedStep, and its full equivalence closure is the original retained-tetrahedron relation. Thus this application proves closedness of that complete original relation, without assuming a replacement kernel or truncating its chains. Freeness, faithfulness and transitivity of the action are unnecessary.")),
                    Paragraph(Text("The retained coordinate carrier is closed in the compact cube [0,three quarters]^4: the four lower and upper inequalities and the finite coordinate sum are continuous closed conditions. Its product with finite discrete Omega is compact. The original TruncatedQuotient therefore inherits compactness from the existing Mathlib compact quotient instance. This argument retains every cap boundary and zero-face tie.")),
                    Paragraph(Text("For the exact quotient projection q and any closed source set C, its saturation q inverse-image of q(C) equals the second projection of R intersected with C times the whole source. The first factor is compact, so isClosedMap_snd_of_compactSpace and the closed relation prove that q is a closed map. Each quotient fiber is the closed relation section at a representative, hence compact. The existing isProperMap_iff_isClosedMap_and_compact_fibers proves that q is proper, and IsProperMap.prodMap makes q times q proper and closed. Its surjectivity and continuity give a quotient map; the preimage of the target diagonal is exactly R. The closed-preimage characterization of a quotient map and t2_iff_isClosed_diagonal then prove that the original retained quotient is Hausdorff. Hausdorffness of that target is not assumed in any of these steps.")),
                    Paragraph(Text("The existing actualSliceQuotientHomeomorph identifies each full original corner quotient with its cap image inside this same TruncatedQuotient, carrying the inherited topology. A subspace of the proved Hausdorff quotient is Hausdorff, and the homeomorphism transfers that property to the actual corner link. This establishes compactness and Hausdorffness of the full retained-tetrahedron quotient, and Hausdorffness of each original corner link. It does not supply the remaining interior or edge-midpoint disk charts, second countability, coherent orientation, global surface identification or Euler/genus count. The application reuses the existing closed-relation theorem and classical topology; it introduces no additional mathematical declaration or novelty claim."))),
                DescribeRole.Theorem),
            Paragraph(Text("The transport description also gives an application to "
                + "the quotient of the same space X=T times K by the same relation R. "
                + "Let J=T times Perm(I), and for j=(t,rho) define the inverse candidate "
                + "B_j(b)=(t,permute(rho inverse,b's carrier)). If R(a,b), the transport "
                + "description supplies rho with b's carrier=permute(rho,a's carrier). "
                + "Choosing j=(a's label,rho) and cancelling the two permutations gives "
                + "a=B_j(b). Thus these finitely many candidates cover every related "
                + "source point for a fixed b. A candidate need not itself be related "
                + "to b; the zero guards and the generating data still determine R.")),
            Paragraph(Text("For a subset C of X, write Sat(C)={b : some a in C "
                + "satisfies R(a,b)}. The candidate cover gives the exact identity "
                + "Sat(C)=union over j in J of [B_j^-1(C) intersect "
                + "(b -> (B_j(b),b))^-1(relationSet(R))], where ^-1 denotes preimage. "
                + "Indeed, a witness a in C related to b equals B_j(b) for some j, "
                + "so b lies in both preimages. Conversely, membership in both "
                + "preimages supplies the witness a=B_j(b) in C with R(a,b). "
                + "The relation factor is essential: membership in B_j^-1(C) "
                + "does not by itself assert R(B_j(b),b).")),
            Paragraph(Text("Each B_j is continuous: coordinate reindexing is "
                + "continuous in the product topology, permutation invariance keeps "
                + "the result in K, and its label is constant. If C is closed in X, "
                + "both preimages in each term are closed, using the closedness of "
                + "relationSet(R) above. Their finite union makes Sat(C) closed. "
                + "Now give Q=X/R its coinduced quotient topology and let pi:X -> Q "
                + "be the canonical projection, so pi(a)=pi(b) exactly when R(a,b). "
                + "Since pi^-1(pi(C))=Sat(C), the defining closed-set criterion for "
                + "this quotient topology shows that pi(C) is closed. Hence pi is "
                + "a continuous closed map on the original space X.")),
            Paragraph(Text("For each y in Q, surjectivity supplies a representative "
                + "b with pi(b)=y. Every a in the exact fiber pi^-1({y}) then "
                + "satisfies R(a,b), so this fiber is a subset of the finite range "
                + "{B_j(b) : j in J}. The fiber is therefore finite and compact. "
                + "Applying Mathlib's proper-map criterion to the continuity and "
                + "closedness of pi and these compact fibers gives properness of pi. "
                + "The criterion imposes no separation assumption on Q; compactness "
                + "here belongs to the fibers, with no compactness, closedness or "
                + "local compactness assumption on S.")),
            Paragraph(Text("Mathlib's product theorem for proper maps now makes "
                + "pi times pi proper, hence closed. Its image of relationSet(R) "
                + "is exactly the diagonal of Q: related pairs have equal images, "
                + "and each diagonal point (y,y) is the image of (b,b) for a "
                + "representative b. Since relationSet(R) is closed, the diagonal "
                + "is closed, and the closed-diagonal criterion gives Hausdorffness "
                + "of Q. This applies the original transport and closed-relation "
                + "result together with the existing Mathlib proper-map and "
                + "separation criteria. Empty T or S gives empty X and Q, and empty "
                + "I leaves no generating seam; the same argument allows all of "
                + "these cases without a nonemptiness assumption.")))));

    private static Formula Statement()
    {
        var t = F.Id("T");
        var i = F.Id("I");
        var a = F.Id("A");
        var s = F.Id("S");
        var coordinates = Maps(i, a);
        var ports = Product(t, i);
        var permutations = Call("Perm", i);
        var invariant = All("rho", permutations, All("z", coordinates,
            Implies(In(F.Id("z"), s),
                In(Call("reindex", F.Id("rho"), F.Id("z")), s))));
        return All("T", F.Id("Types"), All("I", F.Id("Types"),
            All("A", F.Id("Types"), Implies(And(
                Call("Finite", t), Call("Finite", i),
                Call("TopologicalSpace", t), Call("DiscreteTopology", t),
                Call("TopologicalSpace", a), Call("Hausdorff", a), Call("Zero", a)),
                All("S", Call("Sets", coordinates), Implies(invariant,
                    All("next", Maps(ports, t), All("sigma", Maps(ports, permutations),
                        Conclusions()))))))));
    }

    private static Formula Conclusions()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var rho = F.Id("rho");
        var z = F.Id("Z");
        var t = F.Id("T");
        var i = F.Id("I");
        var value = F.Id("A");
        var carrier = F.Id("S");
        var next = F.Id("next");
        var sigma = F.Id("sigma");
        var permutations = Call("Perm", i);
        var finsets = Call("Finsets", i);
        var space = Product(t, Call("Subtype", carrier));
        var state = Product(t, Product(t, Product(permutations, finsets)));
        var seam = Call("seam", t, i, value, carrier, next, sigma);
        var relation = Call("EqvGen", seam);
        var pieces = F.Id("pieces");
        var relationSet = Call("relationSet", relation);
        var uniform = All("a", space, All("b", space,
            Iff(new Formula.Apply(relation, [a, b]), Exists("rho", permutations,
                Exists("Z", finsets, And(
                    Call("guard", t, i, value, carrier, next, sigma,
                        Call("fst", a), Call("fst", b), rho, z),
                    Call("zeroOn", Call("snd", a), z),
                    Eq(Call("snd", b), Call("permute", rho, Call("snd", a)))))))));
        var count = Multiply(Multiply(new Formula.Power(Call("card", t), F.D(2)),
            Call("factorial", Call("card", i))),
            new Formula.Power(F.D(2), Call("card", i)));
        var closedPieces = Exists("pieces", Maps(state, Call("Sets", Product(space, space))),
            And(All("s", state, Call("IsClosed", Call("pieces", F.Id("s")))),
                Eq(relationSet, Call("indexedUnion", pieces, state)),
                Eq(Call("card", state), count)));
        return And(uniform, closedPieces, Call("IsClosed", relationSet));
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Maps(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Product(Formula left, Formula right) =>
        F.Seq(F.Open, left, F.Close, F.Sp, F.Times, F.Sp, F.Open, right, F.Close);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula In(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
