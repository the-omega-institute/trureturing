using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class ActualLinkCornerChainsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Gluing/ActualLinkCornerChains.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original affine link chains: exact point classes and strict-region restriction; compact Hausdorff quotient by ambient closed-relation reuse.",
        H("Actual guarded corner chains"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-link-faceperm"),
                DeclarationHandle.Create(Prefix + "facePerm"), H("The original whole-face permutations"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("facePerm"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four rows are p=(3,0,1,2), q=(3,2,0,1), q inverse and p inverse. The source-owned frozen_face_data proof compares these whole-face maps with the published facePair and slotMap on each actual face slot."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-reverseface"),
                DeclarationHandle.Create(Prefix + "reverseFace"), H("Inverse omitted faces"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("reverseFace"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Faces 0 and 3 are paired; faces 1 and 2 are paired."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-faceword"),
                DeclarationHandle.Create(Prefix + "faceWord"), H("The source group words"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("faceWord"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The source-to-target words are u, v, v inverse, u inverse, in omitted-face order. Multiplication retains the published right-action convention."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-frozen-face-data"),
                DeclarationHandle.Create(Prefix + "frozen_face_data"),
                H("The actual slot map and whole-face extension agree"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("frozen_face_data"))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For each sheet t, each of the four faces f and each of its three slots r, the original facePair is (act(t,faceWord(u,v,f)),reverseFace(f)), and the whole-face permutation sends faceVertex(f,r) to faceVertex(reverseFace(f),slotMap(f,r)). This source-owned comparison supplies the target corner tag for both the original carrier preservation proof and the common-point construction in ActualLinkPathConnected."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-link-raw"),
                DeclarationHandle.Create(Prefix + "Raw"), H("Tagged barycentric coordinates"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Raw"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A raw representative has an actual corner (omega,j) and four real barycentric coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-carrier"),
                DeclarationHandle.Create(Prefix + "Carrier"), H("The complete original corner triangle"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Carrier"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coordinate at j is zero, every coordinate is nonnegative, and their sum is one. The actual corner label is the fixed nu from the frozen Pairing quotient. Boundary ties remain in this closed carrier."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-point"),
                DeclarationHandle.Create(Prefix + "Point"), H("The actual carrier subtype"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Point"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Representatives carry all closed-carrier conditions and the same actual corner-class tag."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-move"),
                DeclarationHandle.Create(Prefix + "move"), H("Original affine face transport"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("move"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Transport the sheet by the exact source word, the omitted corner by the whole-face permutation, and the coordinate vector by its inverse. No endpoints are sorted."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-pairedpoint"),
                DeclarationHandle.Create(Prefix + "pairedPoint"), H("A permitted affine image in the same actual corner class"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("pairedPoint"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The input requires f different from the omitted corner j. The carrier proof directly consumes the published actual_step helper at its original owner, after extending the original face-slot table. The sum and coordinate conditions are preserved by the whole-face permutation. This definition constructs the affine image even away from a side; the Step relation separately imposes the zero guard."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-step"),
                DeclarationHandle.Create(Prefix + "Step"), H("Only the original guarded link generators"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Step"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A step requires f different from j and beta(f)=0, and its target is the displayed affine image. The identically zero omitted-corner coordinate creates no fourth side."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-related"),
                DeclarationHandle.Create(Prefix + "Related"), H("The full original affine equivalence closure"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Related"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take EqvGen of Step on the entire closed carrier. No chart region, assumed cycle or radial-map kernel defines this relation."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-dart"),
                DeclarationHandle.Create(Prefix + "Dart"), H("Ordered endpoint data"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Dart"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The raw ordered occurrence is ((omega,j),k). Actual corner neighborhoods have j different from k because beta(j)=0 and beta(k)>1/2. The data type retains every order, including (3,0)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-dartmove"),
                DeclarationHandle.Create(Prefix + "dartMove"), H("The same whole-face transport on ordered endpoints"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("dartMove"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both j and k move by the actual face permutation; the sheet moves by the actual word."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-dartstep"),
                DeclarationHandle.Create(Prefix + "DartStep"), H("Original oriented edge-incidence transport"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("DartStep"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A dart step may use only a face omitting neither endpoint. This is a generated incidence relation, not an assumed cyclic enumeration."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-dartrelated"),
                DeclarationHandle.Create(Prefix + "DartRelated"), H("The actual ordered-dart component"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("DartRelated"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equivalence closure is generated by the actual guarded endpoint moves. This delivery does not enumerate its component by Fin(3r)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-neighborhood"),
                DeclarationHandle.Create(Prefix + "Neighborhood"), H("Strict corner regions from an actual endpoint component"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Neighborhood"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A representative is selected when some beta(k)>1/2 and its ordered dart is in the actual component of the selected seed. The strict inequality excludes boundary ties from this region while retaining them in Carrier. This delivery proves saturation and chain reflection; it does not yet prove openness or a disk coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-interior"),
                DeclarationHandle.Create(Prefix + "Interior"), H("Interior coordinates"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("Interior"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every non-omitted coordinate is nonzero. On the nonnegative closed carrier this means each of those three coordinates is positive."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-edgepoint"),
                DeclarationHandle.Create(Prefix + "EdgePoint"), H("A unique active side"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("EdgePoint"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Exactly one non-omitted coordinate is zero. The other two are nonzero and, on this carrier, positive."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-link-actual-guarded-point-analysis"),
                DeclarationHandle.Create(Prefix + "actual_guarded_point_analysis"), H("Source-specific normal forms and full-chain restriction"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("actual_guarded_point_analysis"))), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every group, arbitrary right action, u and v, actual corner class nu, and original representatives x and y: an interior x has singleton class; an EdgePoint has exactly x and its distinct original paired image as its class; every strict component neighborhood is invariant under the full EqvGen; and restriction to that neighborhood reflects the full relation. The positive-side proof constructs a two-point invariant from the unique active guard and inverse pairing. It then inducts through all four EqvGen constructors. Saturation is established before the restriction proof, whose transitive case explicitly transports membership to the intermediate representative. These are new original-carrier deductions, not applications of an assumed cycle or assumed relation correspondence. The helpers are consumed on these live proof paths. The remaining local obligations are the four minimal point-period Fin(3r) enumerations, the exact origin-cycle and fan-seam correspondence, openness with the actual quotient-subspace topology, the supplied fan radial chart at the same actual vertex, and the geometric truncation-slice chain and topology comparison. Global orientability, genus, marked-manifold realization and metric statements remain outside this result. No external novelty is claimed."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application: compactness and Hausdorff separation of the full original link quotient. Let G be any group, let Omega be a finite set with the discrete topology, and let G act on the right on Omega, represented in Lean by MulAction Gᵐᵒᵖ Omega. Fix arbitrary u,v in G and nu in Vertex(pairing u v). Use "), Ref(Prefix + "Carrier"), Text(" and "), Ref(Prefix + "Point"), Text(" exactly as defined above: x=((omega,j),beta) has beta(j)=0, beta(i)>=0 for every i, sum beta=1, and label(pairing u v,(omega,j))=nu. The real coordinate space has its product topology, Point has the inherited subtype topology, and Q=Point/Related has the topology induced by its quotient projection. This Q is compact and Hausdorff.")),
            Paragraph(Text("For the ambient application put I=Fin 4, T=Omega times Fin 4, Delta=stdSimplex R I, and X=T times Delta. Write raw((omega,j),beta)=((omega,j),beta) for forgetting the simplex proof, and embed:Point -> X for keeping the same tag and coordinates with their simplex membership. Set p_f=facePerm(f) and w_f=faceWord(u,v,f). For f different from j take next((omega,j),f)=(act(omega,w_f),p_f(j)) and sigma((omega,j),f)=p_f. For f=j take next((omega,j),f)=(omega,j) and sigma((omega,j),f)=id. If permute(rho,beta)(i)=beta(rho inverse(i)), define seam(a,b) by the existence of f with beta_a(f)=0 and b=(next(tag_a,f),permute(sigma(tag_a,f),beta_a)). Coordinate reindexing preserves Delta by nonnegativity and permutation invariance of the sum.")),
            Paragraph(Text("The whole-face maps and words have the original source correspondence: frozen_face_data compares facePerm and faceWord with facePair and slotMap at every actual face slot. Thus a seam at f different from j is precisely the raw image in "), Ref(Prefix + "Step"), Text(" with its original zero guard. A seam at f=j is the identity; it adds only reflexivity to the ambient equivalence closure, not another side identification. No change of action convention, endpoint order, or corner label enters this correspondence.")),
            Paragraph(Text("Let C(a) mean raw(a) belongs to Carrier(u,v,nu). Every seam preserves C in both directions. Forward membership is the carrier property of pairedPoint. For a permitted move through f, the original perm_face identity gives reverseFace(f)=p_f(f), so reverseFace(f) differs from the target omitted corner p_f(j). Applying pairedPoint at that reverse face preserves the target carrier; the original move_inverse identity recovers raw(a). These are the private source facts already used by the original guarded-chain analysis. Identity seams preserve C immediately.")),
            Paragraph(Text("To restrict whole ambient chains, define E(a,b) as the conjunction of C(a) iff C(b) and the assertion that, for every ha:C(a) and hb:C(b), Related(u,v,(raw(a),ha),(raw(b),hb)) holds. E is an equivalence relation: reflexivity and symmetry use the corresponding Related laws; transitivity composes the membership equivalences and the Related proofs. In the transitive case E(a,b), E(b,c), membership ha:C(a) supplies hb:C(b) through the first equivalence before the two subtype relations are composed. This does not assume that arbitrary ambient intermediate points already lie in Carrier.")),
            Paragraph(Text("Each seam lies in E by the preceding membership fact and either Related reflexivity or the original Step constructor. Apply the pinned Relation.EqvGen.eqvGen_le from Mathlib.Logic.Relation with r=seam and r'=E: minimality of equivalence closure gives EqvGen(seam) <= E. Conversely the pullback R(x,y)=EqvGen(seam)(embed(x),embed(y)) is an equivalence relation by IsEquiv.comap, and every original Step lies in R by its displayed affine formula. The same eqvGen_le, now with r=Step and r'=R, gives Related <= R. Projecting the first application onto points of Carrier gives R <= Related. Hence Related(x,y) iff EqvGen(seam)(embed(x),embed(y)) for every pair in the entire original closed carrier.")),
            Paragraph(Text("Apply "), Ref("D5/S3/Geometry/Gluing/FiniteZeroGuardedClosure.uniform_transport_and_closed_relation"), Text(" to these exact T,I,Delta,next,sigma. Its closed-relation component says that EqvGen(seam) is closed in X times X. The indexing states consist of two finite tags, a coordinate permutation and a finite zero footprint; finiteness concerns the family of closed pieces, not the set of related pairs. The continuous embed times embed pulls this closed relation back to the original Related set in Point times Point by the equivalence just established.")),
            Paragraph(Text("Point is compact Hausdorff. Carrier is a closed subset of T times Delta: the omitted coordinate equation beta(j)=0 is closed because the finite discrete tag makes j locally constant, and the fixed label condition is closed in the discrete corner tags. The simplex supplies the nonnegative coordinates and sum equation. Finite T and the closed real standard simplex are compact, so their closed subset is compact by isCompact_stdSimplex and the closed-subset API. The ambient discrete tag and real product spaces are Hausdorff, and so is the subtype Point.")),
            Paragraph(Text("Let q:Point -> Q be the original quotient map. For a closed subset A of Point, its saturation q inverse(q(A)) is the second projection of Related intersect (A times Point). This intersection is closed in the compact product Point times Point; its image is compact and therefore closed in Hausdorff Point. The quotient-topology criterion then makes q a closed map. Each fiber of q is the closed Related class of a representative and is compact. The pinned isProperMap_iff_isClosedMap_and_compact_fibers therefore makes q proper without presupposing that Q is Hausdorff.")),
            Paragraph(Text("IsProperMap.prodMap makes q times q proper and hence closed. It is continuous and surjective, so IsClosedMap.isQuotientMap makes it a quotient map. Its inverse image of the diagonal of Q is exactly Related, already closed; the quotient-map closed-preimage criterion and t2_iff_isClosed_diagonal give T2Space Q. Independently, the continuous surjection q carries compact Point onto Q, giving CompactSpace Q. These steps use the original subtype and quotient topologies throughout.")),
            Paragraph(Text("The application includes all four omitted corners, boundary ties, every actual corner class and degenerate action fibers. The group may be noncommutative; the action need not be faithful, regular, free, transitive or generated by u and v. It supplies compactness and Hausdorffness of this exact quotient. Connectedness, local disk charts, orientability, Euler characteristic, genus and the comparison with a geometric truncation slice require their respective additional arguments.")))));

    private static Formula FormulaFor(string name)
    {
        var x = F.Id("x"); var y = F.Id("y"); var d = F.Id("d");
        var f = F.Id("f"); var g = F.Id("g"); var k = F.Id("k"); var i = F.Id("i");
        var u = F.Id("u"); var v = F.Id("v"); var nu = F.Id("nu");
        var omega = F.Id("Omega"); var fin4 = Call("Fin", F.D(4));
        var point = Call("Point", u, v, nu);
        var corner = Call("corner", x);
        var j = Call("second", corner);
        var betaF = Call("coordinate", x, f);
        var perm = Call("facePerm", f);
        var paired = Call("pairedPoint", u, v, x, f);
        var related = Call("Related", u, v, x, y);
        var neighborhood = Call("Neighborhood", u, v, d);
        Formula X(Formula body) => All("x", point, body);
        Formula XY(Formula body) => X(All("y", point, body));
        return name switch
        {
            "facePerm" => All("f", fin4, All("i", fin4,
                Eq(Call("facePerm", f, i), Call("lookup",
                    Tuple(Tuple(F.D(3),F.D(0),F.D(1),F.D(2)),
                        Tuple(F.D(3),F.D(2),F.D(0),F.D(1)),
                        Tuple(F.D(2),F.D(3),F.D(1),F.D(0)),
                        Tuple(F.D(1),F.D(2),F.D(3),F.D(0))), f, i)))),
            "reverseFace" => All("f", fin4, Eq(Call("reverseFace", f),
                Call("lookup", Tuple(F.D(3),F.D(2),F.D(1),F.D(0)), f))),
            "faceWord" => Scope(All("f", fin4, Eq(Call("faceWord",u,v,f),
                Call("lookup", Tuple(u,v,Call("inverse",v),Call("inverse",u)), f)))),
            "frozen_face_data" => ActionScope(All("t",omega,All("f",fin4,
                All("r",Call("Fin",F.D(3)),And(
                    Eq(Call("facePair",u,v,Pair(F.Id("t"),f)),
                        Pair(Call("act",F.Id("t"),Call("faceWord",u,v,f)),
                            Call("reverseFace",f))),
                    Eq(Call("apply",perm,Call("faceVertex",f,F.Id("r"))),
                        Call("faceVertex",Call("reverseFace",f),
                            Call("slotMap",f,F.Id("r"))))))))),
            "Raw" => All("Omega",F.Id("Type"),
                Eq(Call("Raw",omega), Product(Product(omega,fin4),Call("Functions",fin4,F.Id("R"))))),
            "Carrier" => Scope(All("x",Call("Raw",omega),
                Iff(In(x,Call("Carrier",u,v,nu)), And(
                    Eq(Call("coordinate",x,j),F.D(0)),
                    All("i",fin4,Le(F.D(0),Call("coordinate",x,i))),
                    Eq(Call("sumCoordinates",x),F.D(1)),
                    Eq(Call("label",Call("pairing",u,v),corner),nu))))),
            "Point" => Scope(Eq(point,Call("Subtype",Call("Carrier",u,v,nu)))),
            "move" => Scope(All("f",fin4,All("x",Call("Raw",omega),
                Eq(Call("move",u,v,f,x),
                    Pair(Pair(Call("act",Call("first",corner),Call("faceWord",u,v,f)),
                        Call("apply",perm,j)),Call("pullback",perm,Call("coordinates",x))))))),
            "pairedPoint" => Scope(X(All("f",fin4,Implies(Ne(f,j),
                Eq(Call("value",paired),Call("move",u,v,f,Call("value",x))))))),
            "Step" => Scope(XY(Iff(Call("Step",u,v,x,y),Exists("f",fin4,
                And(Ne(f,j),Eq(betaF,F.D(0)),
                    Eq(Call("value",y),Call("move",u,v,f,Call("value",x)))))))),
            "Related" => Scope(XY(Iff(related,Call("EqvGen",Call("Step",u,v),x,y)))),
            "Dart" => All("Omega",F.Id("Type"),
                Eq(Call("Dart",omega),Product(Product(omega,fin4),fin4))),
            "dartMove" => Scope(All("d",Call("Dart",omega),All("f",fin4,
                Eq(Call("dartMove",u,v,f,d),
                    Pair(Pair(Call("act",Call("sheet",d),Call("faceWord",u,v,f)),
                        Call("apply",perm,Call("firstEndpoint",d))),
                        Call("apply",perm,Call("secondEndpoint",d))))))),
            "DartStep" => Scope(All("d",Call("Dart",omega),All("e",Call("Dart",omega),
                Iff(Call("DartStep",u,v,d,F.Id("e")),Exists("f",fin4,
                    And(Ne(f,Call("firstEndpoint",d)),Ne(f,Call("secondEndpoint",d)),
                        Eq(F.Id("e"),Call("dartMove",u,v,f,d)))))))),
            "DartRelated" => Scope(All("d",Call("Dart",omega),All("e",Call("Dart",omega),
                Iff(Call("DartRelated",u,v,d,F.Id("e")),
                    Call("EqvGen",Call("DartStep",u,v),d,F.Id("e")))))),
            "Neighborhood" => Scope(All("d",Call("Dart",omega),X(
                Iff(In(x,neighborhood),Exists("k",fin4,And(
                    Lt(new Formula.Fraction(F.D(1),F.D(2)),Call("coordinate",x,k)),
                    Call("DartRelated",u,v,d,Pair(corner,k)))))))),
            "Interior" => Scope(X(Iff(Call("Interior",x),
                All("f",fin4,Implies(Ne(f,j),Ne(betaF,F.D(0))))))),
            "EdgePoint" => Scope(X(All("f",fin4,Iff(Call("EdgePoint",x,f),
                And(Ne(f,j),Eq(betaF,F.D(0)),All("g",fin4,
                    Implies(And(Ne(g,j),Eq(Call("coordinate",x,g),F.D(0))),Eq(g,f)))))))),
            "actual_guarded_point_analysis" => Scope(XY(And(
                Implies(Call("Interior",x),Iff(related,Eq(y,x))),
                All("f",fin4,Implies(Call("EdgePoint",x,f),
                    And(Ne(paired,x),Iff(related,Or(Eq(y,x),Eq(y,paired)))))),
                All("d",Call("Dart",omega),Implies(related,
                    Iff(In(x,neighborhood),In(y,neighborhood)))),
                All("d",Call("Dart",omega),Implies(And(In(x,neighborhood),In(y,neighborhood)),
                    Iff(related,Call("EqvGen",Call("StepRestrictedTo",u,v,neighborhood),
                        Call("subtype",x),Call("subtype",y)))))))),
            _ => throw new System.ArgumentOutOfRangeException(nameof(name))
        };
    }
    private static Formula ActionScope(Formula body) =>
        All("G",F.Id("Group"),All("Omega",Call("RightAction",F.Id("G")),
            All("u",F.Id("G"),All("v",F.Id("G"),body))));
    private static Formula Scope(Formula body) =>
        All("G",F.Id("Group"),All("Omega",Call("RightAction",F.Id("G")),
            All("u",F.Id("G"),All("v",F.Id("G"),
                All("nu",Call("Vertex",Call("pairing",F.Id("u"),F.Id("v"))),body)))));
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(name),domain,body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name),[.. args]);
    private static Formula Pair(Formula a, Formula b) => Tuple(a,b);
    private static Formula Tuple(params Formula[] xs)
    {
        var parts = new System.Collections.Generic.List<Formula> { F.Open };
        for (var i = 0; i < xs.Length; i++)
        {
            if (i > 0) { parts.Add(F.Comma); parts.Add(F.Sp); }
            parts.Add(xs[i]);
        }
        parts.Add(F.Close);
        return F.Seq([.. parts]);
    }
    private static Formula Product(Formula a, Formula b) => F.Seq(a,F.Sp,F.Times,F.Sp,b);
    private static Formula And(params Formula[] xs)
    {
        var r = xs[^1];
        for (var i = xs.Length-2; i >= 0; i--) r = new Formula.Logic(xs[i],FormulaLogicOperator.And,r);
        return r;
    }
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Ne(Formula a, Formula b) => F.Seq(a,F.Sp,F.Neq,F.Sp,b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.MemberOf,b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Or,b);
}
