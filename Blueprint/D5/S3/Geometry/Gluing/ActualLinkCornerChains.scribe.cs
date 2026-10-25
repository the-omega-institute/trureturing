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
            Paragraph(Text("Application: an interior chart in the full original link quotient. Let G be any group and let Omega be any discrete topological space carrying the original right G-action, represented by MulAction Gᵐᵒᵖ Omega. Fix u,v in G, an actual corner class nu, and an original representative x=((omega,j),a) in "), Ref(Prefix + "Point"), Text(" satisfying "), Ref(Prefix + "Interior"), Text(". Let Q be the quotient of this entire original Point carrier by "), Ref(Prefix + "Related"), Text(", with its quotient topology, and let q be its original projection. No finiteness assumption on Omega is needed for this interior application.")),
            Paragraph(Text("Write k0=faceVertex(j,0), k1=faceVertex(j,1), k2=faceVertex(j,2). These are exactly the three indices different from j. The original carrier gives a(j)=0, all coordinates nonnegative and sum a=1; Interior makes a(k0), a(k1), a(k2) strictly positive. Set rho=min(a(k0),min(a(k1),a(k2)))/4. Thus rho>0 and each of the three coordinates is at least 4 rho. For another representative y=((eta,l),b), put c(y)=(b(k0)-a(k0))+I*(b(k1)-a(k1)). Define N by the two conditions (eta,l)=(omega,j) and norm(c(y))<rho, and set U=q(N).")),
            Paragraph(Text("The explicit inverse on the radius-rho complex ball sends z to the original tagged representative ((omega,j),b), where b(j)=0, b(k0)=a(k0)+Re(z), b(k1)=a(k1)+Im(z), and b(k2)=a(k2)-Re(z)-Im(z). The three non-omitted coordinates are positive: abs(Re(z)) and abs(Im(z)) are each less than rho, whereas every a(ki) is at least 4 rho. Their sum is one by cancellation, and the unchanged tag keeps the original corner label nu. Consequently this representative belongs to the original Point carrier and satisfies Interior. Its coordinate c is z. Conversely, the omitted-zero and sum-one equations recover the fourth coordinate of every y in N from its first two coordinate differences, so this affine formula recovers y exactly. Both maps are continuous in the inherited subtype topologies.")),
            Paragraph(Text("The set N is open in the original Point carrier: its fixed tag is an open singleton in the discrete tag space Omega times Fin 4, and its complex coordinate norm is a continuous function with a strict cutoff. Every point of N satisfies Interior. Apply the Interior component of "), Ref(Prefix + "actual_guarded_point_analysis"), Text(" at such a point z: for every original representative y, Related(z,y) holds exactly when y=z. Therefore the full saturation q inverse(U) equals N, with no restriction on intermediate representatives in the original EqvGen. This also makes q restricted to N injective. Since q is the original quotient map and N is open and saturated, U is open in Q and the restricted map N -> U is a quotient map. The continuous coordinate map descends through this restriction, and the preceding two inverse identities give a homeomorphism from U to the radius-rho complex ball.")),
            Paragraph(Text("Compose this homeomorphism with scalar division by the positive real number rho, using scalar multiplication as a homeomorphism and restricting it to the corresponding ball subtypes. This gives e:U -> {z in C | norm(z)<1}, a homeomorphism onto the full unit open disk. The original basepoint q(x) belongs to U and e(q(x))=0. For a disk point zeta, e inverse(zeta) is precisely q applied to the same original tagged affine representative with b(j)=0, b(k0)=a(k0)+rho*Re(zeta), b(k1)=a(k1)+rho*Im(zeta), and b(k2)=a(k2)-rho*Re(zeta)-rho*Im(zeta). Thus the inverse is expressed in the original barycentric coordinates, with the original radius, action convention, corner label and full quotient relation.")),
            Paragraph(Text("The construction combines the original singleton-class analysis, finite affine coordinate identities, quotient restriction and descent, and scalar multiplication as a homeomorphism. It applies to arbitrary groups and discrete right-action spaces, without faithful, free, transitive or finite-action hypotheses. It supplies the centered disk chart at Interior points only. It does not supply a chart at EdgePoint representatives, a complete atlas or manifold theorem, orientability, genus, metric data, or a comparison with a geometric truncation slice.")),
            Paragraph(Text("Application: an open-edge chart in the full original link quotient. Let G be any group and let Omega be any discrete topological space with the original right G-action, represented by MulAction Gᵐᵒᵖ Omega. Fix u,v in G, an actual corner class nu, and x=((omega,j),a) in "), Ref(Prefix + "Point"), Text(" with "), Ref(Prefix + "EdgePoint"), Text("(x,f). Thus f differs from j, a(j)=a(f)=0, and the two remaining coordinates are positive. As in the interior application, Q is the quotient of the entire original Point carrier by "), Ref(Prefix + "Related"), Text(", with its original quotient topology, and q is the original projection.")),
            Paragraph(Text("Put sigma=facePerm(f) and retain a source ordering r,s of the two indices outside {j,f}. The source tag is A=(omega,j); the target tag is B=(act(omega,faceWord(u,v,f)),sigma(j)), the tag of "), Ref(Prefix + "pairedPoint"), Text(" applied to x at f. The four original "), Ref(Prefix + "facePerm"), Text(" rows give sigma(j) different from j, so A and B are distinct independently of any freeness of the action. The target side is sigma(f)=reverseFace(f), and its two tangential indices are sigma(r),sigma(s) in that same source order. Set rho=min(a(r),a(s))/4 and a0=a(r)-a(s). Then rho>0 and both a(r) and a(s) are at least 4 rho.")),
            Paragraph(Text("For a representative y with coordinate array b and source tag A, define t=b(r)-b(s)-a0 and n=b(f), and use the signed coordinate F_A(y)=t+I*n. On target tag B, define t=b(sigma(r))-b(sigma(s))-a0 and n=b(sigma(f)), and use F_B(y)=t-I*n. These are the original affine coordinate pullback and an opposite normal sign on the target side. Let N_A consist of source-tag points with norm(F_A)<rho, let N_B consist of target-tag points with norm(F_B)<rho, and put N=N_A union N_B and U=q(N). Each tag fiber is clopen in the original Point carrier, and each strict norm cutoff is open. Hence N is open, with the actual seam points included in its two tagged pieces.")),
            Paragraph(Text("For real t and n with n>=0 and norm(t+I*n)<rho, construct A(t,n) on source tag A by b(j)=0, b(f)=n, b(r)=a(r)+(t-n)/2 and b(s)=a(s)+(-t-n)/2. Since a(r)+a(s)=1, these four coordinates sum to one. The bounds abs(t)<rho and n<rho, together with a(r),a(s)>=4 rho, make the two tangential coordinates strictly positive; all coordinates are nonnegative. The unchanged source tag retains the original label nu. Define B(t,n) by applying the original pairedPoint at f to A(t,n); its tag is B and its coordinate at an index i is the source array evaluated at sigma inverse(i). These constructions lie in the original Point carrier, with A(t,n) in N_A and B(t,n) in N_B, and satisfy F_A(A(t,n))=t+I*n and F_B(B(t,n))=t-I*n. Conversely, the omitted-zero and sum-one equations reconstruct every point in N_A or N_B by these same formulas. Both lifts are continuous on the closed upper half of the radius-rho ball in their inherited subtype topologies.")),
            Paragraph(Text("At n>0, both A(t,n) and B(t,n) satisfy Interior, because the two tangential coordinates and the normal coordinate are positive. At n=0, A(t,0) satisfies EdgePoint at f, and the original "), Ref(Prefix + "Step"), Text(" relates it to B(t,0). Apply "), Ref(Prefix + "actual_guarded_point_analysis"), Text(" to these actual points: the interior representatives have singleton full classes, while the class of A(t,0) is exactly A(t,0) and B(t,0). A full chain starting from B(t,0) is handled by first composing with this original seam step and then applying the same source two-point classification. Thus every full Related class meeting N stays in N, and the signed coordinate F, equal to F_A on N_A and F_B on N_B, has the same value throughout that class. In particular q inverse(U)=N for the full original EqvGen, without an assumed correspondence or any restriction on intermediate representatives.")),
            Paragraph(Text("The function F is continuous on N: its two affine formulas are continuous and its distinct tag pieces are clopen. Since q is the original quotient map and its inverse image of U is the open set N, U is open in Q. Restricting q gives a quotient map N -> U, so the continuous class-invariant F descends to a continuous H:U -> {w in C | norm(w)<rho}. This uses only the original subtype and quotient topologies, and requires no global open-map property of q.")),
            Paragraph(Text("For w=t+I*y in the radius-rho ball, define J(w)=q(A(t,max(y,0))) when y>=0 and J(w)=q(B(t,max(-y,0))) when y<0, with values regarded in U. The two clamped maps are defined and continuous on the entire ball: removing the negative imaginary part, or first reversing its sign and then clamping, cannot increase the complex norm. At y=0 their quotient values agree by the original Step from A(t,0) to B(t,0). Pasting these continuous maps across the zero-imaginary frontier therefore makes J continuous. The signed coordinate identities give H(J(w))=w. Reconstruction gives J(H(q(y)))=q(y) for every representative y in N; the seam case uses precisely that same original Step equality. These identities give a homeomorphism between the actual U and the full radius-rho complex ball.")),
            Paragraph(Text("Rescale by the positive number rho to obtain a homeomorphism e:U -> {zeta in C | norm(zeta)<1} onto the full unit open disk. The source formula gives A(0,0)=x and B(0,0)=pairedPoint(x,f), whose original quotient images agree, so e(q(x))=0. Explicitly, for any disk point zeta put w=rho*zeta, t=Re(w) and y=Im(w). Then e inverse(zeta) is q(A(t,max(y,0))) for y>=0 and q(B(t,max(-y,0))) for y<0, using exactly the original barycentric formulas and affine face transport above. Thus both the chart center and its inverse retain the original representative, right-action convention, corner label and full relation.")),
            Paragraph(Text("This application combines the original point-class analysis with finite affine coordinate identities, quotient restriction and descent, pasting of continuous maps and scalar multiplication as a homeomorphism. It applies to every EdgePoint under an arbitrary group and discrete right-action space, without finite, faithful, free, regular or transitive action hypotheses. Together with the preceding interior application it supplies these two kinds of local chart. It supplies no chart at corner representatives and no complete atlas, manifold theorem, orientability, genus, metric data or comparison with a geometric truncation slice.")),
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
            Paragraph(Text("The application includes all four omitted corners, boundary ties, every actual corner class and degenerate action fibers. The group may be noncommutative; the action need not be faithful, regular, free, transitive or generated by u and v. It supplies compactness and Hausdorffness of this exact quotient. The interior and open-edge charts above use their explicit affine neighborhoods. Charts at corner representatives, a complete atlas, connectedness, a manifold theorem, orientability, Euler characteristic, genus and the comparison with a geometric truncation slice require their respective additional arguments.")))));

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
