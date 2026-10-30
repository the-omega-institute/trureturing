using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;
internal sealed class OriginalReferenceRepeatedMassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "Native mode balance and complete arbitrary-reference operational outputs.",
        H("Loss is the decrease of the surviving mode weight"),Blocks(
            Describe.Lean(DescribeId.Create("native-mode-balance"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.native_mode_balance"),
                H("Every original control and every subinterval"),
                StatementSource.FromAuthor(Disp(Balance())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("Fix c<1/2, 0<a<c and an original height k on [0,T] with constant phase zero. For each original mode i, let p_i(k) be its positive double-wall probability, S(t)=exp(-integral_0^t hazard(c,k)) its native survival, and f_i(t) the squared literal jump amplitude. For every 0<=s<=t<=T, f_i is integrable on (s,t] and its integral equals [S(s)p_i(k(s))-S(t)p_i(k(t))]/p_i(a). No initial-height equality is needed for this general balance law.")),
                    Paragraph(Text("The original regularity alternatives imply absolute continuity of k. OriginalRepeatedMarkedLaw.native_bounds gives 0<k(t)<c on [0,T]; the unordered interval used by almost-everywhere differentiation equals [0,T] because the original control includes T>=0. FiniteRectangleTransport.probability_derivative, at base (c,c,1-2c) and velocity k prime(t), gives p_i prime(t)=direction_i k prime(t), with direction=(1,-1,0,-1,1). The integrable native hazard has an absolutely continuous primitive. Exponentiation preserves absolute continuity on its compact range, and multiplication by each affine probability coordinate preserves it. Almost everywhere, logarithmic differentiation gives g_i=hazard-p_i'/p_i. The explicit five coordinates show g_i>=0. Consequently the literal squared square-root amplitude is g_i S p_i/p_i(a), which is minus the derivative of S p_i divided by p_i(a). The fundamental theorem for absolutely continuous functions gives the balance identity. Exceptional derivative values at corners have zero Lebesgue mass."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("repeated-reference-completeness"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.repeated_reference_completeness"),
                H("The same arbitrary joint input across prefix and suffix"),
                StatementSource.FromAuthor(Disp(Completeness())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("Let B be any band 0<a<b<c<1/2, n>=1 and e either literal early or late history k. Put q=(a/b)(c-b)/(c-a). H is any complete complex Hilbert space, including nonseparable spaces. rho is any positive trace-class operator on Blocks(Fin5,H), with no normalization, finite-rank, separability or product-state assumption. A_i is the positive trace-class compression of that same rho to reference block i. The actual reference-output density is F_i(t)=f_i(t) A_i, as identified with tensor-amplified Kraus conjugation by OriginalReferenceOutputMeasure.repeated_failure_event.")),
                    Paragraph(Text("For every mode i and every 1<t<=2, F_i(t)=q^n F_i^suffix(t-1), where the suffix uses the same rho and the original earlySuffix or lateSuffix control. This is exact prefix scaling of each reference operator, using the already established chronological Kraus action. The coefficient integrals on (0,1], (1,2] and (0,2] are respectively 1-q^n, q^n(1-q) and 1-q^(n+1). In particular the suffix Bochner integral is q^n(1-q) A_i. The endpoint heights and native survival values are supplied by OriginalRepeatedPrefix; they are applied to the general mode balance identity.")),
                    Paragraph(Text("Summing the norms of the five suffix event outputs gives q^n(1-q) norm(rho). Summing the norms of the five full failure event outputs and adding norm(q^(n+1) rho) gives norm(rho). Positivity turns each scalar multiple into its nonnegative coefficient times norm(A_i), and the same-input block trace partition gives sum_i norm(A_i)=norm(rho). Thus all modes and their unchanged reference correlations contribute to exact mass completeness. The terminal scalar is identified with the genuine tensor Kraus conjugation by repeated_live_operational. The six-coordinate extension and the supremum are supplied by repeated_stopped_operational and repeated_operational_supremum.")),
                    Paragraph(Text("These identities retain their unnormalized form; normalized live inputs have norm(rho)=1. The operational companion statements below consume this balance and the corresponding reference-distance theorem."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("repeated-reference-distance"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass.repeated_reference_distance"),
                H("Common prefix cancellation and disjoint suffix windows"),
                StatementSource.FromAuthor(Disp(Distance())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("For every band B, n>=1, arbitrary complete complex Hilbert reference H and positive joint trace-class rho, every mode's prefix Bochner outputs agree on (0,1] intersect every Borel event E. Moreover sum_i integral_(0,2] norm(F_i^early(t)-F_i^late(t)) equals 2 q^n(1-q) norm(rho). Both densities use the same rho, including all entanglement with its unchanged reference.")),
                    Paragraph(Text("Before time one, the literal heights, native survival and jump rates coincide almost everywhere. The seam has zero Lebesgue mass, giving equality on every restricted event. The late suffix is constant before its excursion and the early suffix is constant after its excursion. Local constancy makes both the height derivative and logarithmic probability derivative vanish, so the actual jump coefficient vanishes on the corresponding waiting window. Exact prefix scaling carries these zero densities to the original clock. Except at the middle seam, one of the two suffix densities is zero. Thus the norm of their difference equals the sum of their norms, without comparing independent inputs or replacing joint operators by marginal probabilities.")),
                    Paragraph(Text("Split the full interval into prefix and suffix. The prefix difference integrates to zero, and the suffix norm integral is the sum of the two positive suffix masses. The preceding completeness theorem supplies each mass q^n(1-q) norm(rho). The complete operational companion statements below retain the fixed absorbing successor isometrically, identify the common successful Kraus action, extend to initially stopped six-coordinate states and take the genuine all-input supremum."))),DescribeRole.Theorem),
            Operational("repeated_live_operational", "Complete five-mode classical-quantum output", LiveOperational(),
                "H is any complete complex Hilbert space in any universe, including nonseparable spaces, and rho is any positive trace-class joint input on Blocks(Fin5,H). No normalization, finite rank or product-state assumption is imposed. referenceSuccess is the diagonal original successfulKraus amplified by the unchanged identity reference. The theorem proves both the literal matrix action on the scalar system and its intertwining with TensorProduct.map under the onto Hilbert isometry tensorCoordinates, on every joint tensor vector. successOutput is its actual Kraus conjugation of the same rho. liveFailure embeds the reference compression in the fixed absorbing coordinate f=5, with the squared literal jump amplitude, and is proved equal to absorbingJump rho absorbingJump-adjoint at every time and mode.",
                "At the terminal time two, both actual successful operators equal sqrt(q^(n+1)) times the identity. Hence their successful outputs agree for the same arbitrary rho. liveDistance is exactly the IS.7 half-sum: the trace norm of the successful-output difference plus the sum over all five modes of the Lebesgue integral on (0,2] of the trace norm of the full absorbing-output-density difference. The fixed f embedding preserves the norm of each signed scalar multiple of its positive reference block. Applying repeated_reference_distance therefore gives liveDistance=q^n(1-q) norm(rho). Neither the mode/time record nor any reference correlation is discarded."),
            Operational("repeated_stopped_operational", "The original six-dimensional absorbing extension", StoppedOperational(),
                "The input is an arbitrary positive trace-class rho on Blocks(Fin6,H), with any complete complex Hilbert reference H. stoppedSuccess is exactly K direct-sum the stopped identity: its first five coordinates use the original diagonal K, and coordinate five is unchanged. The theorem gives its tensor intertwining and explicit coordinate action. stoppedJump is the rank-one literal jump extended by zero on stopped input. Its tensor intertwining is proved on every joint tensor vector; every jump annihilates insertion into f. stoppedFailure is proved equal to that actual tensor-amplified Kraus conjugation of rho, at every time and original mode. For either repeated history, these full output densities are Bochner integrable on (0,2] intersect every Borel event E.",
                "The successful six-coordinate outputs are identical for the same original rho. In particular, arbitrary initial live-stopped coherences are retained in A rho A-adjoint, and cancel only because the two terminal A operators are equal. liveWeight is the sum of the norms of the five positive diagonal reference compressions. Positivity identifies these with their real traces, and the existing finite-block trace partition proves liveWeight plus the stopped block trace equals norm(rho). To reuse the five-mode distance result, diagonalLive embeds these same five blocks into a positive five-mode auxiliary operator. Its compression in mode i is exactly the original six-coordinate compression in i.castSucc, and its norm is liveWeight. Only the failure calculation uses this auxiliary operator; the successful output continues to act on the original rho. Thus stoppedDistance=q^n(1-q) liveWeight. For every normalized six-coordinate input, liveWeight is at most one, so stoppedDistance is at most q^n(1-q)."),
            Operational("repeated_operational_supremum", "All references, attainment and the original marked law", SupremumOperational(),
                "JointState(m) packages a reference H in an arbitrary fixed universe, its complete complex Hilbert instances, and a positive joint trace-class input of norm one on Blocks(Fin m,H). operationalDistance is the real supremum of the actual stoppedDistance values of all JointState(6) inputs in that universe. Its definition contains no proposed scalar. The previous theorem bounds every such input, including infinite-dimensional and nonseparable references. A one-dimensional lifted reference and an input supported in live coordinate zero provide a positive normalized fully live witness, with liveWeight one and distance q^n(1-q). The identity on this one-dimensional reference has trace and trace norm one by the existing finite-multiplicity trace theorem. Thus the independently defined supremum equals q^n(1-q) in every universe. The theorem also gives this value for every normalized five-live-mode input, and links the supremum to OriginalRepeatedMarkedLaw.native_marked_tv for every common unknown beta, integer parity m and initial phase vector theta.",
                "The inverse application uses that exact operational/marked equality at every n in OriginalRepeatedMarkedLaw.marked_inverse_nonuniformity. The actual height gap remains b-a while q^n(1-q) tends to zero, defeating every modulus tending to zero at the origin on the fixed-duration, common-band class. OriginalRepeatedResources supplies the same literal controls with their finite-piecewise-C1 regularity and exact aggregate resources: duration two, height variation and arc length 2(n+1)(b-a), zero phase variation, squared-speed integral (4n^2+8)(b-a)^2, height essential speed max(2n,4)(b-a), and zero phase speed. These values agree within each compared pair and grow with n. The obstruction applies to the class without a common speed or height-variation cap. No law acquisition, waveform sensor, reset, unexecuted-tail read or additional programme register is supplied."))));
    private static DocumentBlock Operational(string name,string title,Formula f,string p,string q)=>Describe.Lean(
        DescribeId.Create(name.Replace('_','-')),DeclarationHandle.Create("D5/S3/Quantum/Fibers/OriginalReferenceRepeatedMass."+name),
        H(title),StatementSource.FromAuthor(Disp(f)),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(p)),Paragraph(Text(q))),DescribeRole.Theorem);
    private static Formula LiveOperational()
    {
        Formula h=F.Id("H"),b=F.Id("B"),n=F.Id("n"),rho=F.Id("rho"),e=F.Id("e");
        Formula k=C("literalEarlyLate",b,n,e),mass=Mul(Mul(Pow(C("q",b),n),Sub(D(1),C("q",b))),C("norm",rho));
        Formula matrix=All([V("c",R),V("a",R),V("k",R),V("s",R),V("x",C("EuclideanSpace",D(5))),V("i",C("Fin",D(5)))],
            Eq(C("coordinate",C("referenceSuccess",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("s"),F.Id("x")),F.Id("i")),
                C("coordinate",C("mulVec",C("successfulKraus",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("s")),F.Id("x")),F.Id("i"))));
        Formula terminal=All([V("e",F.Id("Bool"))],Eq(C("referenceSuccess",b,C("apply",k,D(2)),C("survival",b,k,D(2))),
            C("smul",C("sqrt",Pow(C("q",b),Add(n,D(1)))),C("identity",C("Blocks",D(5),h)))));
        return All([V("H",F.Id("CompleteComplexHilbertSpace")),V("B",F.Id("OriginalSupportBand")),V("n",F.Id("Natural")),V("rho",C("PositiveJointTraceClass",D(5),h))],
            Imp(C("atLeastOne",n),And(TensorSuccess(5,"referenceSuccess"),And(matrix,And(ActualFailure(5,"liveFailure","absorbingJump",rho),And(terminal,Eq(Distance("liveDistance",b,n,rho),mass)))))));
    }
    private static Formula StoppedOperational()
    {
        Formula h=F.Id("H"),b=F.Id("B"),n=F.Id("n"),rho=F.Id("rho"),e=F.Id("e"),i=F.Id("i"),ev=F.Id("E");
        Formula mass=Mul(Pow(C("q",b),n),Sub(D(1),C("q",b))),weight=C("liveWeight",rho),dist=Distance("stoppedDistance",b,n,rho);
        Formula kill=All([V("c",R),V("a",R),V("k",R),V("s",R),V("g",C("Function",C("Fin",D(5)),R)),V("i",C("Fin",D(5))),V("x",h)],
            Eq(C("apply",Jump("stoppedJump"),C("insertion",D(5),F.Id("x"))),D(0)));
        Formula successEq=Eq(C("stoppedSuccessOutput",b,C("literalEarly",b,n),rho),C("stoppedSuccessOutput",b,C("literalLate",b,n),rho));
        Formula tensorJump=All([V("c",R),V("a",R),V("k",R),V("s",R),V("g",C("Function",C("Fin",D(5)),R)),V("i",C("Fin",D(5))),V("z",C("HilbertTensor",C("EuclideanSpace",D(6)),h))],
            Eq(C("apply",Jump("stoppedJump"),C("tensorCoordinates",F.Id("z"))),C("tensorCoordinates",C("TensorMapIdentityReference",C("scalarSystem",Jump("stoppedJump")),F.Id("z")))));
        Formula coords=All([V("c",R),V("a",R),V("k",R),V("s",R),V("x",C("Blocks",D(6),h))],And(
            All([V("i",C("Fin",D(5)))],Eq(C("coordinate",C("apply",Success("stoppedSuccess"),F.Id("x")),C("castSucc",i)),
                C("smul",C("successfulDiagonal",F.Id("c"),F.Id("a"),F.Id("k"),F.Id("s"),i),C("coordinate",F.Id("x"),C("castSucc",i))))),
            Eq(C("coordinate",C("apply",Success("stoppedSuccess"),F.Id("x")),D(5)),C("coordinate",F.Id("x"),D(5)))));
        Formula events=All([V("e",F.Id("Bool")),V("i",C("Fin",D(5))),V("E",C("Set",R))],Imp(C("MeasurableSet",ev),
            C("IntegrableOn",C("stoppedFailure",b,C("literalEarlyLate",b,n,e),i,rho),C("intersection",C("Ioc",D(0),D(2)),ev))));
        return All([V("H",F.Id("CompleteComplexHilbertSpace")),V("B",F.Id("OriginalSupportBand")),V("n",F.Id("Natural")),V("rho",C("PositiveJointTraceClass",D(6),h))],
            Imp(C("atLeastOne",n),And(TensorSuccess(6,"stoppedSuccess"),And(ActualFailure(6,"stoppedFailure","stoppedJump",rho),And(kill,And(successEq,And(Eq(dist,Mul(mass,weight)),And(Imp(Eq(C("norm",rho),D(1)),new Formula.Relation(dist,FormulaRelationOperator.LessThanOrEqual,mass)),And(tensorJump,And(coords,events))))))))));
    }
    private static Formula SupremumOperational()
    {
        Formula u=F.Id("U"),b=F.Id("B"),n=F.Id("n"),rho=F.Id("rho"),mass=Mul(Pow(C("q",b),n),Sub(D(1),C("q",b)));
        Formula op=C("operationalDistance",u,b,C("literalEarly",b,n),C("literalLate",b,n));
        Formula live=All([V("rho",C("JointState",u,D(5)))],Eq(Distance("liveDistance",b,n,rho),mass));
        Formula witness=new Formula.BindMany(FormulaQuantifier.Exists,[V("rho",C("JointState",u,D(6)))],And(Eq(C("liveWeight",rho),D(1)),Eq(Distance("stoppedDistance",b,n,rho),mass)));
        Formula marked=All([V("beta",R),V("m",F.Id("Integer")),V("theta",C("Function",C("Fin",D(5)),R))],Eq(
            C("eventTV",C("markedLaw",b,F.Id("beta"),F.Id("m"),F.Id("theta"),C("literalEarly",b,n)),C("markedLaw",b,F.Id("beta"),F.Id("m"),F.Id("theta"),C("literalLate",b,n))),op));
        return All([V("U",F.Id("UniverseLevel")),V("B",F.Id("OriginalSupportBand")),V("n",F.Id("Natural"))],Imp(C("atLeastOne",n),And(live,And(witness,And(Eq(op,mass),marked)))));
    }
    private static Formula TensorSuccess(byte d,string name)=>All([V("c",R),V("a",R),V("k",R),V("s",R),V("z",C("HilbertTensor",C("EuclideanSpace",D(d)),F.Id("H")))],
        Eq(C("apply",Success(name),C("tensorCoordinates",F.Id("z"))),C("tensorCoordinates",C("TensorMapIdentityReference",C("scalarSystem",Success(name)),F.Id("z")))));
    private static Formula Success(string name)=>C(name,F.Id("c"),F.Id("a"),F.Id("k"),F.Id("s"));
    private static Formula Jump(string name)=>C(name,F.Id("c"),F.Id("a"),F.Id("k"),F.Id("s"),F.Id("g"),F.Id("i"));
    private static Formula ActualFailure(int d,string output,string jump,Formula rho)=>All([V("c",R),V("a",R),V("k",C("Function",R,R)),V("i",C("Fin",D(5))),V("t",R)],
        Eq(C("underlying",C(output,F.Id("c"),F.Id("a"),F.Id("k"),F.Id("i"),rho,F.Id("t"))),
            C("KrausConjugation",C(jump,F.Id("c"),F.Id("a"),C("apply",F.Id("k"),F.Id("t")),C("survival",F.Id("c"),F.Id("k"),F.Id("t")),C("jumpRate",F.Id("c"),F.Id("k"),F.Id("t")),F.Id("i")),rho)));
    private static Formula Distance(string name,Formula b,Formula n,Formula rho)=>C(name,b,D(2),C("literalEarly",b,n),C("literalLate",b,n),rho);
    private static Formula Balance()
    {
        Formula c=F.Id("c"),a=F.Id("a"),t=F.Id("t"),s=F.Id("s"),k=F.Id("k"),i=F.Id("i"),cap=F.Id("T");
        Formula density=C("modeCoefficient",c,a,k,i);
        Formula mass=Div(Sub(Mul(C("survival",c,k,s),C("p",c,C("apply",k,s),i)),Mul(C("survival",c,k,t),C("p",c,C("apply",k,t),i))),C("p",c,a,i));
        Formula assumptions=And(C("lt",c,Div(D(1),D(2))),And(C("memIoo",a,D(0),c),And(C("OriginalConstantPhaseControl",c,cap,k),C("orderedSubinterval",s,t,D(0),cap))));
        return All([V("c",R),V("a",R),V("T",R),V("k",C("Function",R,R)),V("i",C("Fin",D(5))),V("s",R),V("t",R)],Imp(assumptions,And(C("IntegrableOn",density,C("Ioc",s,t)),Eq(C("integral",density,C("Ioc",s,t)),mass))));
    }
    private static Formula Completeness()
    {
        Formula b=F.Id("B"),n=F.Id("n"),e=F.Id("e"),rho=F.Id("rho"),i=F.Id("i"),t=F.Id("t"),q=C("q",b);
        Formula k=C("literalEarlyLate",b,n,e),suffix=C("literalSuffix",b,e),qn=Pow(q,n),qnext=Pow(q,Add(n,D(1))),mass=Mul(qn,Sub(D(1),q));
        Formula density=C("modeCoefficient",b,k,i),output=C("modeOutput",b,k,i,rho),ai=C("referenceCompression",rho,i);
        Formula scaling=All([V("t",R)],Imp(C("memIoc",t,D(1),D(2)),Eq(C("apply",output,t),C("smul",qn,C("apply",C("modeOutput",b,suffix,i,rho),Sub(t,D(1)))))));
        Formula modes=All([V("i",C("Fin",D(5)))],And(scaling,And(Eq(C("integral",density,C("Ioc",D(0),D(1))),Sub(D(1),qn)),And(Eq(C("integral",density,C("Ioc",D(1),D(2))),mass),And(Eq(C("integral",density,C("Ioc",D(0),D(2))),Sub(D(1),qnext)),Eq(C("integral",output,C("Ioc",D(1),D(2))),C("smul",mass,ai)))))));
        Formula sumSuffix=C("sumModeOutputIntegralNorms",b,k,rho,C("Ioc",D(1),D(2)));
        Formula sumFull=C("sumModeOutputIntegralNorms",b,k,rho,C("Ioc",D(0),D(2)));
        Formula body=And(modes,And(Eq(sumSuffix,Mul(mass,C("norm",rho))),Eq(Add(sumFull,C("norm",C("smul",qnext,rho))),C("norm",rho))));
        return All([V("H",F.Id("CompleteComplexHilbertSpace")),V("B",F.Id("OriginalSupportBand")),V("n",F.Id("Natural")),V("e",F.Id("Bool")),V("rho",C("PositiveJointTraceClass",F.Id("H")))],Imp(C("atLeastOne",n),body));
    }
    private static Formula Distance()
    {
        Formula b=F.Id("B"),n=F.Id("n"),rho=F.Id("rho"),i=F.Id("i"),ev=F.Id("E"),q=C("q",b);
        Formula early=C("literalEarly",b,n),late=C("literalLate",b,n);
        Formula fe=C("modeOutput",b,early,i,rho),fl=C("modeOutput",b,late,i,rho);
        Formula domain=C("intersection",C("Ioc",D(0),D(1)),ev);
        Formula prefix=All([V("i",C("Fin",D(5))),V("E",C("Set",R))],Imp(C("MeasurableSet",ev),Eq(C("integral",fe,domain),C("integral",fl,domain))));
        Formula distance=C("sumModesIntegralNormDifference",b,early,late,rho,C("Ioc",D(0),D(2)));
        Formula mass=Mul(Mul(D(2),Mul(Pow(q,n),Sub(D(1),q))),C("norm",rho));
        return All([V("H",F.Id("CompleteComplexHilbertSpace")),V("B",F.Id("OriginalSupportBand")),V("n",F.Id("Natural")),V("rho",C("PositiveJointTraceClass",F.Id("H")))],Imp(C("atLeastOne",n),And(prefix,Eq(distance,mass))));
    }
    private static Formula Sub(Formula a,Formula b)=>Subtract(a,b);
    private static Formula Mul(Formula a,Formula b)=>Multiply(a,b);
    private static Formula Div(Formula a,Formula b)=>C("divide",a,b);
    private static Formula Pow(Formula a,Formula b)=>C("power",a,b);
    private static readonly Formula R=F.Id("Real");
    private static Formula.BoundVariable V(string n,Formula t)=>new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula.BoundVariable[] xs,Formula f)=>new Formula.BindMany(FormulaQuantifier.ForAll,[..xs],f);
    private static Formula Eq(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Imp(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula C(string n,params Formula[] xs)=>new Formula.FunctionCall(FormulaIdentifier.Create(n),[..xs]);
}
