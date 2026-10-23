using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.Gluing;

internal sealed class ActualLinkAffineFanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/Gluing/ActualLinkAffineFan.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual ordered-corner occurrences carry strict affine sector coordinates.",
        H("Actual strict-sector affine coordinates"),
        Blocks(
            Def("Sector", "The strict triangle sector",
                "The two real coordinates are nonnegative and their sum is strictly less than one. This is the open radial part of the closed triangle, with both seam edges and the origin retained."),
            Def("beta", "Source barycentric coordinates",
                "For row c and phase s, the omitted corner has coordinate zero, the ordered tip has coordinate 1-(a+b)/2, the incoming face has a/2, and the outgoing face has b/2. The four labels are distinct in each of the twelve actual ordered endpoint positions."),
            Def("vertex", "The actual seed corner class",
                "The vertex is the original pairing label of the corner of encode(u,v,c,(x,0)). All four rows retain the source order L0, L1, H2, H0, and ordered pairs such as (3,0) are not sorted."),
            Def("rawPhi", "Finite occurrence coordinates",
                "The index lies in Fin(3r), where r is the minimal point period of the original row return word at x. Its actual dart is occurrence(u,v,c,x,i). The phase of the corresponding iterate of tour determines the incoming and outgoing face coordinates. No return of the full transported frame is required."),
            Def("Phi", "The strict original neighborhood",
                "Restrict a and b to nonnegative reals with a+b<1. The constructed raw point lies in the original Carrier at the actual seed vertex and in Neighborhood of the actual seed dart. Its ordered tip has barycentric coordinate strictly greater than one half. The cutoff a+b=1 is outside this chart; it is not removed from the ambient carrier."),
            Describe.Lean(DescribeId.Create("actual-strict-coordinate-bijection"),
                DeclarationHandle.Create(Prefix + "actual_strict_coordinates"),
                H("Unique actual occurrence and affine coordinates"),
                StatementSource.FromAuthor(F.Disp(FormulaFor("actual_strict_coordinates"))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any group G, any finite set Omega with a right G action, any u and v, any one of the four rows, and any root x, Phi bijectively parametrizes the genuine strict original neighborhood. There is no assumption that G is finite, that the action is faithful, free, transitive or regular, or that the return word has finite group order.")),
                    Paragraph(Text("The inverse first finds the unique barycentric coordinate greater than one half. The original ordered-dart component enumeration then determines the unique occurrence index. The two real coordinates are twice the original incoming and outgoing barycentric coordinates. The simplex equation and zero omitted-corner coordinate prove that their sum is strictly less than one and reconstruct every original barycentric entry.")),
                    Paragraph(Text("The original pairedPoint construction transports the corner label along each guarded dart step; EqvGen induction transports it along the complete dart component. This puts Phi at the same actual link vertex, not at an independently chosen label. The finite-period supplier covers singleton period one, giving three occurrences, as well as nonfaithful and nonregular actions.")),
                    Paragraph(Text("The guarded generator calculation below identifies exactly the positive strict-sector seams and their reverses. Full original chains reflect to the strict neighborhood before being transported through the coordinate bijection. The topology below is induced from the original discrete corner labels and real barycentric coordinates. The closed fan comparison below reflects every intermediate chain through the strict radius cutoff. The exact original radial norm identity now supplies the closed-fan restriction and the open unit disk chart. The literal affine cap map below also identifies the full original corner carrier and relation with its cap image in the full original truncated quotient. Global orientability, closedness, genus and geometric conclusions remain separate.")),
                    Paragraph(Text("The source is the actual link application accompanying supplement 122.3 of the group-transport construction. ActualCornerPointPeriods supplies the entire original dart component, and ActualLinkCornerChains supplies the original guarded affine carrier. The cyclic fan disk theorem is an existing further supplier; no generic circle or disk theorem is proved here. No literature-priority claim is made."))),
                DescribeRole.Theorem),
            Def("sector_count_neZero", "Positive point-period sector count",
                "The actual point period is positive. Consequently the cyclic index type Fin(3r) has nonzero size, including r=1."),
            Def("swap", "Exchange of seam coordinates",
                "Swapping a and b preserves nonnegativity and the strict radial bound."),
            Def("seam", "Positive cyclic seam",
                "The outgoing zero edge (i,a,0) is identified with (i+1,0,a), with positive cyclic wrap."),
            Thm("actual_step_iff", "Exact original guarded generators",
                "For every two strict-sector inputs, the original Step between their Phi images holds exactly when one input is a positive seam successor of the other. The omitted-corner guard excludes that face and strict tip positivity excludes the tip face. The two remaining source permutations exchange the incoming and outgoing coordinate roles. Their actual group-action transport and minimal point-period wrap supply the successor and predecessor occurrences."),
            Thm("actual_eqvgen_iff", "Full original chains and strict fan chains",
                "The full original affine EqvGen between two Phi images equals the equivalence generated by the positive strict fan seams. Saturation and reflection in ActualLinkCornerChains retain every intermediate original representative. The constructed bijection transports the restricted chain, and each source generator becomes a seam or its reverse by actual_step_iff. No relation correspondence is a hypothesis."),
            Def("closedInput", "Strict sectors in the closed fan carrier",
                "The inclusion retains the index and both real coordinates, weakening only the strict radial bound to its non-strict ambient bound."),
            Thm("actual_full_fan_correspondence", "The full original closed-fan equivalence",
                "For strict inputs, the full original affine EqvGen equals the original CyclicTriangleDisk EqvGen after inclusion in its closed carrier. Every closed-fan seam preserves a+b. Equivalence-closure induction therefore keeps every intermediate representative inside the strict cutoff, and reflects the full closed chain to the strict seam chain. The displayed fanRelated denotes the original CyclicTriangleDisk.Related, retaining its generator-defined fan relation."),
            Def("coordinateEquiv", "The actual strict coordinate equivalence",
                "This is the equivalence determined by the constructed bijection Phi. Its inverse selects the actual occurrence and its two original affine coordinates."),
            Def("coordinateHomeomorph", "Original induced coordinate topology",
                "With discrete Omega, the coordinate equivalence is a homeomorphism for the induced carrier topology. A fiber of the inverse occurrence index fixes the original corner label and imposes a strict dominant-tip inequality, hence is open. The remaining inverse coordinates are twice the incoming and outgoing barycentric entries. This proves both directions of continuity without an assumed homeomorphism."),
            Def("ActualQuotient", "The full original affine quotient",
                "The quotient uses the original guarded Step and its full equivalence closure on Carrier at the actual seed vertex. Its topology is the quotient topology of the original carrier."),
            Def("quotientNeighborhood", "Actual quotient neighborhood",
                "Take the image of the strict original neighborhood in the full original quotient, carrying its subspace topology. The displayed quotientMk is its canonical quotient projection."),
            Thm("actual_open_quotient_neighborhood", "Open saturated image and restricted quotient map",
                "The full original chain-saturation theorem gives q inverse of q(N) equal to N. The strict neighborhood N is open: it is a union of strict coordinate inequalities intersected with discrete ordered-corner component conditions. By the quotient topology q(N) is open, and the restriction of q over q(N) is a quotient map. No global openness or Hausdorff property of the actual quotient is assumed."),
            Def("actualSeamQuotientHomeomorph", "Actual strict quotient topology",
                "The established coordinate homeomorphism and full relation equivalence identify the quotient of strict sectors by the positive seams with the open image in the full original quotient. The restricted actual quotient map supplies exactly its original subspace topology."),
            Def("OpenDisk", "The open unit disk", "Complex norm strictly less than one, with the induced topology."),
            Def("actualOpenDiskChart", "An actual open disk chart", "The chart composes the original strict seam quotient homeomorphism with the restriction of the existing closed radial homeomorphism. The newly public radial_norm is consumed directly; its statement and proof are unchanged. The domain is the open image in the full original quotient and carries its inherited topology."),
            Paragraph(Text("For the order-halving application, let G and H be finite groups with their canonical regular right multiplication actions and discrete topologies. Fix a homomorphism pi:G -> H and a marked pair u,v in G. Put ell=v inverse times u squared, and assume ell has order four while pi(ell) has order two. Use row zero and root one in the original ordered-endpoint construction. The source neighborhood uses twelve sectors and the corresponding target neighborhood uses six. These orders are hypotheses about the marked return word; no global surjectivity, centrality or kernel-size premise is needed for the following collision argument.")),
            Paragraph(Text("The original carrier map sends ((g,j),beta) to ((pi(g),j),beta), retaining every one of the four real coordinates. Its corner label is transported by the quotient map induced by g -> pi(g). The actual face words commute with pi, so this map preserves each original guarded Step, including its zero-coordinate guard, and therefore the full generated equivalence relation. The induced map F is continuous on the full original link quotient for the selected source corner-vertex label, with values in the quotient for its transported label. These are their original quotient topologies. The source corner-vertex label maps to the target row-zero/root-one corner-vertex label.")),
            Paragraph(Text("In the twelve-sector source neighborhood, compare sector indices zero and six on the two diagonal curves specified below. They have the same phase. Their sheet coordinates are one and ell squared, respectively. For t>0, both triangle coordinates are positive, so the complete original fan correspondence gives distinct cyclic normal forms for these two represented classes inside the strict neighborhood. The actual source classes are therefore different. Their target raw representatives agree: pi(ell squared)=one, and all four coordinates were retained.")),
            Paragraph(Text("For each of these two sectors take a=b=max(0,min(t,1/4)). The resulting curve is continuous for all real t, lies in the strict original neighborhood, equals the literal endpoint at t=0, and has both coordinates positive for every t>0. Any open neighborhood of that endpoint pulls back along both curves to an open neighborhood of zero. Their intersection contains a positive t, giving two distinct points in that same open neighborhood with equal F-images. Thus F is not locally injective at the original endpoint, and cannot be a local homeomorphism or a covering map on the full original link quotient.")),
            Paragraph(Text("This argument establishes collisions arbitrarily close to the specified original endpoint. Exact two-element punctured fibers, a punctured covering theorem, the other endpoint rows, and the ambient three-dimensional retained-tetrahedron map require further arguments. The identification of the full inverse image of the chosen target neighborhood is not established here, and no global kernel size is assumed. The local collision conclusion does not assume those stronger statements.")),
            Def("TruncatedTetrahedron", "The original retained tetrahedron", "All four coordinates are between zero and three quarters inclusive, and their sum is one. Every cap and zero-face tie is retained. This is the literal carrier of Original Link Interface section 5.1 with delta=1/4."),
            Def("TruncatedPoint", "Original tetrahedron copies", "The original tetrahedron index in Omega is retained alongside all four affine coordinates."),
            Def("truncatedMove", "The original whole-face transport", "The source tetrahedron t moves to act(t,faceWord(u,v,face)); target coordinate i is source coordinate facePerm(f) inverse of i. These are precisely the same original four permutations and words, including both inverse directions."),
            Def("TruncatedStep", "The original ambient face guard", "A generator is allowed exactly when alpha_f=0 and the target is truncatedMove. There is no extra slice or corner guard in the ambient relation."),
            Def("Slice", "The actual labeled cap component", "A point lies in the slice at nu when some coordinate j equals three quarters and the original corner (t,j) has label nu. Nonnegative coordinates summing to one force this cap index to be unique."),
            Def("alpha", "Literal affine cap coordinates", "The map is alpha=(3/4)e_j+(1/4)beta, on the complete original corner triangle beta_j=0, beta nonnegative, sum beta=1."),
            Def("toTruncation", "The actual affine carrier map", "Retain t and use alpha at the actual corner j. The original corner label determines the cap component."),
            Thm("actual_slice_carriers", "Full carrier equivalence", "The map into Slice is bijective. The inverse recovers the unique cap index j and sets beta_j=0 and beta_i=4 alpha_i for i different from j. The complete carrier includes all boundary ties, with no strict cutoff imposed on this comparison."),
            Thm("actual_slice_step_iff", "Exact slice generators", "Original Step holds if and only if ambient TruncatedStep holds between the affine images. The positive cap coordinate excludes the omitted corner face automatically. For every other face alpha_f=0 is equivalent to beta_f=0. Alpha commutes with the actual coordinate permutation, and pairedPoint preserves the original corner label."),
            Thm("actual_slice_eqvgen_iff", "Full ambient chain reflection", "The equivalence holds for the full original ambient EqvGen, not merely for chains assumed to stay in the slice. Each ambient generator preserves slice membership in both directions. In the backward direction its cap coordinate is pulled through the inverse permutation; the original pairedPoint construction transports the label, and uniqueness of the cap index recovers the specified label. EqvGen induction then retains every transitive intermediate before transporting the chain through the carrier bijection."),
            Def("actualSliceHomeomorph", "Actual carrier topology", "With finite discrete Omega, the original full corner carrier is compact and the original cap subspace is Hausdorff. The literal affine carrier bijection is continuous, hence a homeomorphism. Both topologies are inherited from the actual labels and real coordinate arrays."),
            Def("TruncatedQuotient", "The full original truncated quotient", "The quotient is generated by TruncatedStep on all original retained tetrahedra, with its quotient topology."),
            Def("quotientSlice", "The original cap image", "Take the image of Slice under the full ambient quotient projection, with its inherited topology."),
            Def("actualSliceQuotientHomeomorph", "The full original quotient comparison", "Full-chain invariance proves that the inverse image of the cap image is exactly Slice. Slice is a finite union of closed cap-coordinate and discrete-label conditions, so its quotient image is closed. The closed-subspace quotient criterion supplies the restricted quotient map. Composing it with the actual carrier homeomorphism and exact full relation theorem yields the displayed homeomorphism. No quotient correspondence or slice invariance is an assumption. This does not identify the retained quotient with the separately specified marked manifold in main theory 70.10."))));


    private static DocumentBlock.Describe Thm(string name, string heading, string text) =>
        Describe.Lean(DescribeId.Create("actual-link-affine-" + name.Replace('_','-')),
            DeclarationHandle.Create(Prefix + name), H(heading),
            StatementSource.FromAuthor(F.Disp(FormulaFor(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static DocumentBlock.Describe Def(string name, string heading, string text) =>
        Describe.Lean(DescribeId.Create("actual-link-affine-" + name.ToLowerInvariant().Replace('_','-')),
            DeclarationHandle.Create(Prefix + name), H(heading),
            StatementSource.FromAuthor(F.Disp(FormulaFor(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula FormulaFor(string name)
    {
        var g=F.Id("G"); var o=F.Id("Omega"); var u=F.Id("u"); var v=F.Id("v");
        var c=F.Id("c"); var x=F.Id("x"); var s=F.Id("s"); var p=F.Id("p");
        var l=F.Id("l"); var z=F.Id("z"); var w=F.Id("w");
        var f4=Call("Fin",F.D(4)); var f3=Call("Fin",F.D(3));
        var index=Call("Fin",Product(F.D(3),Call("pointPeriod",u,v,c,x)));
        var source=Product(index,F.Id("Sector"));
        var seed=Call("encode",u,v,c,Tuple(x,F.D(0)));
        var phase=Call("second",Call("iterate",Call("tour",u,v,c),Call("value",Call("first",z)),Tuple(x,F.D(0))));
        var raw=Tuple(Call("first",Call("occurrence",u,v,c,x,Call("first",z))),
            Call("beta",c,phase,Call("value",Call("second",z))));
        var target=Call("Neighborhood",u,v,Call("vertex",u,v,c,x),seed);
        Formula Scope(Formula body) => All("G",F.Id("Type"),All("Omega",F.Id("Type"),
            F.Seq(F.OpenBracket,Call("Group",g),F.CloseBracket,F.Sp,
                F.OpenBracket,Call("MulAction",Call("Opposite",g),o),F.CloseBracket,F.Sp,
                All("u",g,All("v",g,All("c",f4,All("x",o,body)))))));
        var a=Call("first",p); var b=Call("second",p);
        var betaValue=Call("if",Eq(l,Call("tip",c,s)),
            Call("subtract",F.D(1),Call("divide",Call("add",a,b),F.D(2))),
            Call("if",Eq(l,Call("incoming",c,s)),Call("divide",a,F.D(2)),
                Call("if",Eq(l,Call("outgoing",c,s)),Call("divide",b,F.D(2)),F.D(0))));
        var imageZ=Call("value",Call("Phi",u,v,c,x,z));
        var imageW=Call("value",Call("Phi",u,v,c,x,w));
        var n=Product(F.D(3),Call("pointPeriod",u,v,c,x));
        var q=Call("quotientMk",Call("EqvGen",Call("Step",u,v,Call("vertex",u,v,c,x))));
        var qn=Call("quotientNeighborhood",u,v,c,x);
        Formula Discrete(Formula f) => F.Seq(
            F.OpenBracket,Call("TopologicalSpace",o),F.CloseBracket,F.Sp,
            F.OpenBracket,Call("DiscreteTopology",o),F.CloseBracket,F.Sp,f);
        var nu=F.Id("nu"); var j=F.Id("j"); var i=F.Id("i"); var face=F.Id("f");
        var aa=F.Id("a"); var bb=F.Id("b"); var pp=F.Id("p"); var qq=F.Id("q");
        var coords=Call("Functions",f4,F.Id("Real"));
        var threeFourths=Call("divide",F.D(3),F.D(4));
        Formula Le(Formula left,Formula right) => new Formula.Relation(left,FormulaRelationOperator.LessThanOrEqual,right);
        Formula Exists(string binderName,Formula domain,Formula body) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(binderName),domain,body);
        Formula UV(Formula body) => All("G",F.Id("Type"),All("Omega",F.Id("Type"),
            F.Seq(F.OpenBracket,Call("Group",g),F.CloseBracket,F.Sp,
                F.OpenBracket,Call("MulAction",Call("Opposite",g),o),F.CloseBracket,F.Sp,
                All("u",g,All("v",g,body)))));
        Formula AtNu(Formula body) => UV(All("nu",Call("Vertex",Call("pairing",u,v)),body));
        var carrier=Call("Point",u,v,nu); var slice=Call("Slice",u,v,nu);
        var trunc=Call("TruncatedPoint",o); var tx=Call("toTruncation",u,v,pp); var ty=Call("toTruncation",u,v,qq);
        Formula Both(Formula body) => AtNu(All("p",carrier,All("q",carrier,body)));
        Formula Top(Formula body) => Implies(Call("Finite",o),Discrete(body));
        return name switch
        {
            "Sector" => All("p",Product(F.Id("Real"),F.Id("Real")),
                Iff(Call("member",p,F.Id("Sector")),And(
                    F.Seq(F.D(0),F.Sp,F.Le,F.Sp,a),F.Seq(F.D(0),F.Sp,F.Le,F.Sp,b),
                    Lt(Call("add",a,b),F.D(1))))),
            "beta" => All("c",f4,All("s",f3,All("p",Product(F.Id("Real"),F.Id("Real")),
                All("l",f4,Eq(Call("beta",c,s,p,l),betaValue))))),
            "vertex" => Scope(Eq(Call("vertex",u,v,c,x),Call("label",Call("pairing",u,v),Call("first",seed)))),
            "rawPhi" => Scope(All("z",source,Eq(Call("rawPhi",u,v,c,x,z),raw))),
            "Phi" => Scope(Implies(Call("Finite",o),All("z",source,And(
                Call("member",Call("Phi",u,v,c,x,z),target),
                Eq(Call("underlyingRaw",Call("Phi",u,v,c,x,z)),raw))))),
            "actual_strict_coordinates" => Scope(Implies(Call("Finite",o),
                Call("Bijective",Call("Phi",u,v,c,x)))),
            "sector_count_neZero" => Scope(Implies(Call("Finite",o),Call("NeZero",n))),
            "swap" => All("p",F.Id("Sector"),Eq(Call("value",Call("swap",p)),
                Tuple(Call("second",Call("value",p)),Call("first",Call("value",p))))),
            "seam" => All("n",F.Id("Nat"),Implies(Call("NeZero",F.Id("n")),
                All("z",Product(Call("Fin",F.Id("n")),F.Id("Sector")),
                All("w",Product(Call("Fin",F.Id("n")),F.Id("Sector")),
                Iff(Call("seam",z,w),And(Eq(Call("second",Call("value",Call("second",z))),F.D(0)),
                    Eq(w,Tuple(Call("add",Call("first",z),F.D(1)),Call("swap",Call("second",z)))))))))),
            "actual_step_iff" => Scope(Implies(Call("Finite",o),All("z",source,All("w",source,
                Iff(Call("Step",u,v,imageZ,imageW),new Formula.Logic(Call("seam",z,w),
                    FormulaLogicOperator.Or,Call("seam",w,z))))))),
            "actual_eqvgen_iff" => Scope(Implies(Call("Finite",o),All("z",source,All("w",source,
                Iff(Call("EqvGen",Call("Step",u,v),imageZ,imageW),
                    Call("EqvGen",F.Id("seam"),z,w)))))),
            "closedInput" => All("n",F.Id("Nat"),All("z",Product(Call("Fin",F.Id("n")),F.Id("Sector")),
                Eq(Call("closedInput",z),Tuple(Call("first",z),Call("closedTriangle",Call("value",Call("second",z))))))),
            "actual_full_fan_correspondence" => Scope(Implies(Call("Finite",o),All("z",source,All("w",source,
                Iff(Call("EqvGen",Call("Step",u,v),imageZ,imageW),
                    Call("fanRelated",Call("closedInput",z),Call("closedInput",w))))))),
            "coordinateEquiv" => Scope(Implies(Call("Finite",o),And(
                Call("Equivalence",Call("coordinateEquiv",u,v,c,x),source,target),
                Eq(Call("forward",Call("coordinateEquiv",u,v,c,x)),Call("Phi",u,v,c,x))))),
            "coordinateHomeomorph" => Scope(Implies(Call("Finite",o),Discrete(And(
                Call("Homeomorphism",Call("coordinateHomeomorph",u,v,c,x),source,target),
                Eq(Call("forward",Call("coordinateHomeomorph",u,v,c,x)),Call("Phi",u,v,c,x)))))),
            "ActualQuotient" => Scope(Eq(Call("ActualQuotient",u,v,c,x),
                Call("Quotient",Call("Carrier",u,v,Call("vertex",u,v,c,x)),
                    Call("EqvGen",Call("Step",u,v))))),
            "quotientNeighborhood" => Scope(Eq(qn,Call("image",q,target))),
            "actual_open_quotient_neighborhood" => Scope(Discrete(And(
                Eq(Call("preimage",q,qn),target),Call("IsOpen",qn),
                Call("IsQuotientMap",Call("restrictPreimage",qn,q))))),
            "actualSeamQuotientHomeomorph" => Scope(Implies(Call("Finite",o),Discrete(
                Call("Homeomorphism",Call("actualSeamQuotientHomeomorph",u,v,c,x),
                    Call("Quotient",source,Call("EqvGen",F.Id("seam"))),qn)))),
            "OpenDisk" => All("z",F.Id("Complex"),Iff(Call("member",z,F.Id("OpenDisk")),Lt(Call("norm",z),F.D(1)))),
            "actualOpenDiskChart" => Scope(Top(Call("Homeomorphism",Call("actualOpenDiskChart",u,v,c,x),qn,F.Id("OpenDisk")))),
            "TruncatedTetrahedron" => All("a",coords,Iff(Call("member",aa,F.Id("TruncatedTetrahedron")),And(All("i",f4,And(Le(F.D(0),Call("eval",aa,i)),Le(Call("eval",aa,i),threeFourths))),Eq(Call("sum",aa),F.D(1))))),
            "TruncatedPoint" => All("Omega",F.Id("Type"),Eq(trunc,Product(o,F.Id("TruncatedTetrahedron")))),
            "truncatedMove" => UV(All("f",f4,All("a",trunc,And(Eq(Call("first",Call("truncatedMove",u,v,face,aa)),Call("act",Call("first",aa),Call("faceWord",u,v,face))),All("i",f4,Eq(Call("coordinate",Call("truncatedMove",u,v,face,aa),i),Call("coordinate",aa,Call("inverseApply",Call("facePerm",face),i)))))))),
            "TruncatedStep" => UV(All("a",trunc,All("b",trunc,Iff(Call("TruncatedStep",u,v,aa,bb),Exists("f",f4,And(Eq(Call("coordinate",aa,face),F.D(0)),Eq(bb,Call("truncatedMove",u,v,face,aa)))))))),
            "Slice" => AtNu(All("a",trunc,Iff(Call("member",aa,slice),Exists("j",f4,And(Eq(Call("coordinate",aa,j),threeFourths),Eq(Call("label",Call("pairing",u,v),Tuple(Call("first",aa),j)),nu)))))),
            "alpha" => All("j",f4,All("b",coords,All("i",f4,Eq(Call("alpha",j,bb,i),Call("add",Call("if",Eq(i,j),threeFourths,F.D(0)),Call("divide",Call("eval",bb,i),F.D(4))))))),
            "toTruncation" => AtNu(All("p",carrier,Eq(tx,Tuple(Call("tetrahedron",pp),Call("alpha",Call("corner",pp),Call("coordinates",pp)))))),
            "actual_slice_carriers" => AtNu(Call("Bijective",Call("codRestrict",Call("toTruncation",u,v),slice),carrier,slice)),
            "actual_slice_step_iff" => Both(Iff(Call("Step",u,v,pp,qq),Call("TruncatedStep",u,v,tx,ty))),
            "actual_slice_eqvgen_iff" => Both(Iff(Call("EqvGen",Call("Step",u,v),pp,qq),Call("EqvGen",Call("TruncatedStep",u,v),tx,ty))),
            "actualSliceHomeomorph" => AtNu(Top(And(Call("Homeomorphism",Call("actualSliceHomeomorph",u,v,nu),carrier,slice),Eq(Call("forward",Call("actualSliceHomeomorph",u,v,nu)),Call("codRestrict",Call("toTruncation",u,v),slice))))),
            "TruncatedQuotient" => UV(Eq(Call("TruncatedQuotient",u,v,o),Call("Quotient",trunc,Call("EqvGen",Call("TruncatedStep",u,v))))),
            "quotientSlice" => AtNu(Eq(Call("quotientSlice",u,v,nu),Call("image",Call("truncatedQuotientMk",u,v),slice))),
            "actualSliceQuotientHomeomorph" => AtNu(Top(Call("Homeomorphism",Call("actualSliceQuotientHomeomorph",u,v,nu),Call("Quotient",carrier,Call("EqvGen",Call("Step",u,v))),Call("quotientSlice",u,v,nu)))),
            _ => throw new System.ArgumentOutOfRangeException(nameof(name))
        };
    }

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(name),domain,body);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(F.Id(name),[.. args]);
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
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Iff,b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
}
