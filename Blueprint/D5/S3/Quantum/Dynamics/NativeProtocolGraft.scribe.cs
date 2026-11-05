using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;
internal sealed class NativeProtocolGraftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stop-aware composition of the original sixteen-bit native protocols.",
        H("Native protocol composition and original-record projection"),
        Blocks(Describe.Lean(DescribeId.Create("original-native-projection"),
            DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_native_projection"),
            H("Every original path retains its matrix, archive and resource semantics"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/chiribella2009networks")),
            Blocks(
                Paragraph(Text("The carrier Basis is the set of all functions from Fin 16 to Bool, with shifted sites 0 through 15 representing the original sites -1 through 14. All operators are full matrices on these 65536 basis words. The root Omega is the computational word with ones at shifted positions 0, 4 and 8. No factorization of the 2584-dimensional legal subspace is used.")),
                Paragraph(Text("The menu is that of V88 definitions 23.1, 23.2 and 28.1. It uses the actual fourteen golden matrices K at addresses 0 through 13: Q is t times the zero-number projection plus t squared times the number projection plus beta cubed times bit flip; P is the product of neighboring number projections plus the product of their complements times Q; K is zeta times identity plus zeta times (zeta minus one) times P. Here phi=(1+sqrt(5))/2, t=phi inverse, beta=sqrt(t), and zeta=exp(3 pi i/5). An inverse call is interpreted as nine forward calls and costs nine. A forward call costs one.")),
                Paragraph(Text("A finite native tree has gate nodes, finite complete diagonal measurement nodes and labeled leaves. A measurement is specified by a function from Basis to Fin n: outcome o has the diagonal projector whose entries are one exactly on the fiber of o. Surjectivity is unnecessary, so zero projectors and their full successor trees remain. Feedback can depend on the whole acquired path. Leaf labels distinguish active cuts from absorbed stops; each stop has its failure, refusal, early or normal kind and its own identifying code.")),
                Paragraph(Text("For prefix T, Continuations(T) means the full function type Path(T) to Fin 2 to Tree(Stop). RecordEvent(T) means all Boolean predicates on the tuple of a natural program identifier, an original Path(T), an optional Fin 2 read and a Stop, together with a terminal Basis word. For such a continuation table C, E(p) denotes extension(T,C,p). At an active leaf E first reads original bit b1, at shifted index 2, and then executes C(p,j). At an absorbed leaf E is the single original stopped leaf: its operator is identity, its archive is empty, its added cost is zero and its read tag is none. CutLaw states these two cases, including each active read tag, diagonal projector, archive entry and terminal stop label.")),
                Paragraph(Text("G is graft(T,E). Each G path has a unique split into the original path p and an added path q of E(p), with inverse attach(T,E,p,q). The original-record projection keeps the original program pi, the full original path p, the optional original read j, the final stop and every terminal basis word z. Original path identities are retained even when two paths have equal labels or zero mass. Only the added path q is summed out. The event e is any Boolean predicate on this retained record and z.")),
                Paragraph(Text("Op denotes the chronological branch matrix; Ar is the complete gate-and-report archive; c is the expanded forward-call cost; L is its maximum over every syntactic terminal path. Mass uses normSq of Op applied to the same fixed Omega. The first equality is a raw finite Born-mass pushforward. It does not divide by success probability or erase records physically. The second equality includes every zero, failing and stopped path; it allows different continuation costs at different original leaves.")),
                Paragraph(Text("The path bijection and matrix factorization follow by induction through every original gate and measurement node. Reindexing the complete terminal sum by that bijection gives the event equality. The same induction concatenates archives and adds expanded costs. Taking the maximum over the finite, nonempty continuation fibers gives the exact whole-tree resource equality.")),
                Paragraph(Text("This composition theorem does not establish total Born-mass normalization, arithmetic integrality or nonphysical-conjugate estimates for the actual native gates. It does not construct a Petz compiler, compute the actual chi reference, or prove either numerical obstruction or resource lower bound. Those conclusions require their respective native arithmetic and reference-state bridges. No protection of the complement of b1, auxiliary preparation, reset, new controlled operation or postselection is assumed."))),
            DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-event-arithmetic"),
                DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_arithmetic"),
                H("Integral raw event masses exclude both reference-comparison values"),
                StatementSource.FromAuthor(ArithmeticStatement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
                Blocks(
                    Paragraph(Text("For every type L of terminal labels, every finite full-menu native tree T and every Boolean event e on its complete terminal path and terminal sixteen-bit word, the raw mass p=eventMass(T,e) is an algebraic integer over the ordinary integers. All fourteen actual gate addresses, deterministic feedback, complete diagonal zero-one measurements, zero outcomes, stops and expanded inverse calls are included. The input is the same fixed computational root Omega; no arbitrary input vector or external probability weights occur.")),
                    Paragraph(Text("The scalars t, beta and zeta of the actual matrices are algebraic integers: rational-angle exponential and cosine integrality give zeta and t, and beta squared equals t. Every number projection and bit flip has integer entries. Finite matrix addition, multiplication and powers therefore preserve entrywise integrality. Induction through the actual tree gives integral branch-matrix entries. Applying the fixed root, multiplying each amplitude by its physical complex conjugate and summing the selected raw events preserve integrality. The real event mass is reflected from its injective complex embedding. No success normalization is performed.")),
                    Paragraph(Text("Set q=(13-5 sqrt(5))/22 and w=(9 sqrt(5)-19)/22. In the existing quadratic golden field with generator phi, these are the images of coordinate pairs (9/11,-5/11) and (-14/11,9/11). Their field norms are respectively 1/11 and -1/11. Integrality would force an integer field norm; both rational values fail that condition. Consequently p differs from both q and w. This argument only needs absolute algebraic integrality of p and does not assert that p lies in the quadratic field.")),
                    Paragraph(Text("These exclusions apply directly to any original-record event formed by the stop-aware graft above. They do not establish that the actual chi preparation and its faithful-support Petz pullback have ideal masses q and w. Quadratic integer coordinates, the whole-tree nonphysical-conjugate estimate and the arithmetic factor-eleven bounds are supplied below. The actual reference-state realization, original-record comparison and total-variation consumers remain separate obligations. Total Born-mass normalization and the equality of the ninth gate power with its inverse are not used or proved here."))),
                DescribeRole.Theorem), CoordinateNode(), ResourceNode(), EmptyPetzNode())));


    private static DocumentBlock CoordinateNode() => Describe.Lean(
        DescribeId.Create("original-event-coordinates-and-bound"),
        DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_coordinates_and_bound"),
        H("Computed integer coordinates and the whole-tree signed conjugate bound"),
        StatementSource.FromAuthor(CoordinateStatement()),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
        Blocks(
            Paragraph(Text("For every terminal-label type L, original native tree T and Boolean terminal event e, coordinates(T,e) is an explicitly computed integer pair A,B in the inverse-golden basis. The physical evaluation is A+B t, with t=phi inverse; its other real evaluation is A-B phi. The displayed theorem identifies the first value with the actually computed raw eventMass, identifies the second value with a signed sum over the same terminal paths and basis words, and bounds its absolute value using L(T)=Tree.maxCalls(T) and kappa=1+2 phi cubed.")),
            Paragraph(Text("The coefficient ring O consists of integer pairs with generator tau satisfying tau squared equals one minus tau. S consists of two O coordinates with generator eta satisfying eta squared equals minus one minus tau eta. These are Mathlib quadratic algebras; their multiplication and both evaluation homomorphisms are proved from the displayed equations. At each full basis word z the coefficient vector h represents the actual amplitude as beta to exponent(z) times physical(h(z)). The exponent is zero or one according to the Hamming parity relative to the actual root at shifted positions 0,4,8. A center-bit flip changes that parity.")),
            Paragraph(Text("The forward update is diagStep(j,z) h(z) plus offStep(j,z) tau to (one minus exponent(z)) h(flip(j,z)). Here diagStep is eta times one plus (eta minus one) times the actual diagonal of P; offStep is tau eta (eta minus one) on the 00 neighboring-control block and zero elsewhere. The proof expands the original number projections and bit flip on all sixteen-bit words and all fourteen addresses. Branch transport follows the original chronological operator product, with nine updates for inverse syntax. A report multiplies each coefficient by its original selector indicator, and all report outcomes remain in the tree.")),
            Paragraph(Text("For H=a+b eta, its quadratic norm in S is a squared minus tau a b plus b squared. The event coordinates sum tau to exponent(z) times this norm only on the selected original terminal coordinates. Under the physical evaluation this is exactly the original squared amplitude. Under tau mapped to minus phi, eta mapped to exp(pi i/5), and beta mapped to i sqrt(phi), it equals minus one to exponent(z) times the embedded squared amplitude. This sign is essential: the second evaluation is not a positive Born mass. No field-membership certificate or assumed event law is present.")),
            Paragraph(Text("The embedded active block has squared operator bound phi to the sixth, obtained by two-coordinate Cauchy-Schwarz and reindexing by the same center-bit involution. The remaining control blocks are zero or identity. The gate norm is therefore at most kappa. Induction on the complete tree sums all measurement energies before comparing the child maxima with the original maximum; selector completeness gives exact energy conservation even for non-surjective selectors. This proves a whole-tree bound with no leaf, report or branch-count factor. Zero-mass deep branches and nine-cost calls retain their syntactic resource cost.")),
            Paragraph(Text("The cut-determinant construction is a pending extension of the existing coefficient representation. Its complete original-cut correspondence remains unverified; the existing event theorem does not establish this route. The formulas below specify the required correspondence and do not add a theorem or coverage claim.")),
            Paragraph(Text("For the original cut-determinant application, fix any subset I of the sixteen positions, and split a basis word into its restrictions r on I and z on its complement. This includes the empty and full subsets. For every actual tree T and acquired-history event e, Xi(r,s) is the sum over selected histories h and the same complementary word z of c_h(r,z) times the physical conjugate of c_h(s,z). Each c_h is the existing actual branch product on the fixed root; branch_physical supplies its coefficient representation beta to exponent(r,z) times physical(F_h(r,z)), with F_h computed by branch(T,h,initial). No arbitrary matrix or assumed quadratic-membership certificate is used.")),
            Paragraph(Text("Work in the free integral coefficient algebra K=S[B]/(B squared minus tau), over the existing S and O=Z[tau]. This is a coordinate algebra, not a constructed degree-eight field. The beta-sign involution fixes S and sends B to minus B. Physical conjugation instead fixes B and conjugates both S coefficients using eta sent to minus tau minus eta. These two explicitly defined maps commute. Evaluation sends B to the original beta and uses the same existing t and zeta on S; beta squared equals t verifies the homomorphism law. Applying it to each computed branch coefficient gives the original c_h, so entrywise evaluation of the coefficient cut matrix gives the original Xi exactly.")),
            Paragraph(Text("The Hamming parity of the full word splits into its I parity and complementary parity relative to the same fixed root. In a reduced entry, the complementary word occurs twice. Therefore the beta-sign map sends the coefficient cut matrix to J Xi_K J, where J is the diagonal row-parity sign matrix and J squared is identity. The distinct physical conjugation sends Xi_K to its transpose. The pinned RingHom.map_det, Matrix.det_mul and Matrix.det_transpose identities then make its determinant fixed under both maps. In the two nested quadratic coordinates, the first invariance forces the B coefficient to vanish; the second forces the remaining cyclotomic imaginary coefficient to vanish. The surviving coordinate x=A+B_0 tau is computed from that same determinant, with A and B_0 integers.")),
            Paragraph(Text("Once the two fixed-coordinate identities and actual evaluation correspondence are verified, the physical determinant D equals A+B_0 t and is integral over the integers, using the existing t_integral. This would apply the existing branch representation and pinned algebra identities, with no additional D5 binding declaration. Reuse norm_product and norm_zero in Coeff for x: the product of D and its other real evaluation A minus B_0 phi equals the integer norm A squared minus A B_0 minus B_0 squared. If D is nonzero this norm is nonzero, and int_abs_lower gives one less than or equal to the absolute value of D times that same other evaluation. The intended domain is every original position subset and acquired-history event, including zero events; it exceeds the existing b1 calibration result.")),
            Paragraph(Text("This descent does not bound the other determinant evaluation by kappa to twice Ld. That actual same-tree estimate, its extension/restriction correspondence with the nonphysical branch coefficients, the determinant resource lower bound and both minimum-eigenvalue bounds remain separate obligations of source theorem 24.1. The physical complete-tree normalization and arbitrary-position cut trace are supplied separately by NativeProtocolBornNormalization; the faithful conditional calibration still requires its original consumers. No claim that arbitrary embeddings commute with physical conjugation is used.")),
            Paragraph(Text("This event theorem does not identify an original cut reduction or prove its determinant or spectral lower bounds. It does not construct the actual chi state, Petz comparison, full record-law bridge or Born normalization, and it does not prove that the ninth gate power is the semantic inverse."))),
        DescribeRole.Theorem);

    private static DocumentBlock ResourceNode() => Describe.Lean(
        DescribeId.Create("original-event-resource-bounds"),
        DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_event_resource_bounds"),
        H("Positive-event and factor-eleven arithmetic resource bounds"),
        StatementSource.FromAuthor(ResourceStatement()),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
        Blocks(
            Paragraph(Text("The bounds apply to every actually computed eventMass of the same original tree T. K denotes kappa to twice Tree.maxCalls(T). Every positive raw event mass is at least one divided by K. For q=emptyTarget=(13-5 sqrt(5))/22 and w=referenceTarget=(9 sqrt(5)-19)/22, the two displayed discrepancy bounds use exactly the source constants and the same K. These are arithmetic bounds for raw masses, without conditioning or a probability-normalization premise.")),
            Paragraph(Text("For x=A+B tau the integer norm is A squared minus A B minus B squared, and the product of its two real evaluations equals that norm. Its nonvanishing is reused from the existing golden-integer norm theorem through the coordinate correspondence (A-B,B). For u=11q=(4,-5) and u=11w=(-5,9), the norms are 11 and minus 11. Direct expansion proves that the norm of 11x-u is divisible by 11. The existing original_event_arithmetic theorem supplies non-equality with q and w. Thus the nonzero norm has absolute value at least 11. The whole-tree conjugate bound and the triangle inequality give the stated denominators.")),
            Paragraph(Text("The arithmetic inequalities do not identify q or w as the ideal probabilities of the actual chi/Petz experiments. Their empty-prefix and five-call source-history realization, preservation of original records and failure zeros, graft resource identities and total-variation comparison still require the specified original-object consumers. The cut determinant and spectral clauses of V88 theorem 24.1 remain outside this event result."))),
        DescribeRole.Theorem);

    private static DocumentBlock EmptyPetzNode() => Describe.Lean(
        DescribeId.Create("original-empty-petz-consumer"),
        DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolGraft.original_empty_petz_consumer"),
        H("Actual faithful calibration and the original empty-input Petz event"),
        StatementSource.FromAuthor(EmptyPetzStatement()),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
        Blocks(
            Paragraph(Text("Use the same full sixteen-bit carrier, root, fourteen addresses, selectors and stop-aware continuations defined above. The source tree is exactly the chronological three forward calls K3,K2,K1, ending at an active cut. The bijection cut splits shifted bit 2, the original b1, from all fifteen remaining bits. Reduced(v) is the existing partialTraceRight of the rank-one full-carrier matrix, reindexed only by this bijection. This mathematical reduction adds no physical deletion, state preparation or protection of the complement.")),
            Paragraph(Text("The actual gate action on a computational vector has its original diagonal coefficient and one possible center-flip coefficient. Applying it three times to the original root gives a squared times b at 000, a times b squared at 100, zeta times a times c at 001, zeta times b times c at 101, and zeta times b squared at 010, with all other native bits unchanged. Here a=-t, b=-beta times zeta to the fourth, c=-t times zeta cubed. The partial trace contracts equal complement words. It gives chi exactly, with entries t,gamma,conjugate gamma,t squared, where gamma=t squared times beta times conjugate of zeta to the fourth. These weights are computed from that same pure native vector.")),
            Paragraph(Text("The theorem proves that chi is positive definite, has trace one and determinant t to the fourth. Its positive square root is chiRoot=(chi+t squared I)/sqrt(1+2t squared). Positivity of the actual partial trace and uniqueness of the positive square root are reused directly. No faithfulness or square-root identity is assumed. The source tree has exactly three expanded forward calls.")),
            Paragraph(Text("For every full-carrier vector v, summing the two reduced outputs of the actual original b1 projectors gives delta(Reduced(v)), where delta(X) is the diagonal matrix with entries Xii. Each original j output remains a distinct branch; this equality is their mathematical marginal. The empty original root reduces to P0. Its actual j=0 projected vector is the same root and its j=1 vector is zero.")),
            Paragraph(Text("The fixed mathematical Petz map is petz(Y)=sqrt(chi) delta(W Y W) sqrt(chi), with W the existing continuous functional calculus of inverse square root at delta(chi). The existing diagonal functional-calculus theorem identifies W with diag(beta inverse,t inverse). Direct evaluation on the actual empty-root reduction gives petz(Reduced(Omega))11=q=(13-5sqrt(5))/22=t to the fourth divided by (1+2t squared). This is an ideal comparison value, not a native operation or an assumed input probability.")),
            Paragraph(Text("For every complete original continuation table C from the native b1 read to trees of Stop labels, let T=extensionAt(active,C). For the actual terminal event z1=1, summing all acquired paths and terminal complement words, eventMass(T,e) differs from the real part of that same Petz entry and obeys the displayed factor-eleven lower bound. The maximum is that of the complete syntactic tree, including zero, failure and stopped outcomes. The proof consumes original_event_arithmetic and original_event_resource_bounds at this actual T and event. No arbitrary event-mass surrogate, conditioning or success normalization is introduced.")),
            Paragraph(Text("This consumer establishes the three-call calibration and empty-input comparison. The original five-call prefix K3,K2,K1,K10,K13 with every X,Y archive and retained j, its ideal w value, the full identity extension on the complement and original records, failure-zero law and total-variation consumers remain open. Full V88 theorem 24.1 still requires its actual cut determinant and spectral bounds. NativeProtocolBornNormalization supplies the separate complete-tree Born law and arbitrary-position acquired-event cut trace. The semantic identity of the ninth gate power with its inverse remains unproved here. The fixed source obligations are not narrowed to this consumer."))),
        DescribeRole.Theorem);

    private static Formula EmptyPetzStatement()
    {
        Formula v=F.Id("v"), j=F.Id("j"), C=F.Id("C");
        Formula root=Call("omegaZero"), chi=Call("chi"), R=Call("Reduced",root);
        Formula projected=Call("mulVec",Call("projector",Call("readBit",D(2)),j),v);
        Formula emptyProjected=Call("mulVec",Call("projector",Call("readBit",D(2)),j),root);
        Formula native=All("v",Call("FullVector"),
            Rel(FiniteSum(j,Call("Fin",D(2)),Call("Reduced",projected)),Eq,Call("delta",Call("Reduced",v))));
        Formula empty=All("j",Call("Fin",D(2)),
            Rel(emptyProjected,Eq,IfThenElse(Rel(j,Eq,D(0)),root,D(0))));
        Formula T=Call("extensionAt",Call("active"),C);
        Formula ev=Call("terminalBitOne",D(2));
        Formula mass=Call("eventMass",T,ev), q=Call("Re",Call("entry",Call("petz",R),D(1),D(1)));
        Formula K=Power(Call("kappa"),Seq(D(2),Star,Call("maxCalls",T)));
        Formula conjugate=Seq(Frac,Grp(D(1,3),Plus,D(5),Sqrt,Grp(D(5))),Grp(D(2,2)));
        Formula bound=Leq(Seq(Frac,Grp(D(1)),Grp(D(1,1),Star,Parenthesized(Seq(K,Plus,conjugate)))),
            Call("abs",Seq(mass,Minus,q)));
        Formula allContinuations=All("C",Call("Function",Call("Fin",D(2)),Call("Tree",Call("Stop"))),
            And(new Formula.Relation(mass,FormulaRelationOperator.NotEqual,q),bound));
        return Disp(And(
            Rel(Call("Reduced",Call("mulVec",Call("Op",Call("sourceTree"),Call("unit")),root)),Eq,chi),
            Rel(Call("calls",Call("sourceTree"),Call("unit")),Eq,D(3)),
            Call("PosDef",chi),Rel(Call("trace",chi),Eq,D(1)),
            Rel(Call("det",chi),Eq,Power(Call("t"),D(4))),
            Rel(Call("cfc",Call("sqrt"),chi),Eq,Call("chiRoot")),
            native,Rel(R,Eq,Call("P0")),empty,
            Rel(Call("entry",Call("petz",R),D(1),D(1)),Eq,Call("complex",Call("emptyTarget"))),
            allContinuations));
    }

    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Power(Formula a, Formula b) => Seq(Grp(Parenthesized(a)), Caret, Grp(b));
    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula CoordinateStatement()
    {
        Formula L=F.Id("L"), T=F.Id("T"), e=F.Id("e"), p=F.Id("p"), z=F.Id("z");
        Formula x=Call("coordinates",T,e), nu=Call("realConjugate",x);
        Formula signed=Seq(Power(Grp(Minus,D(1)),Call("exponent",z)),Star,
            Call("normSq",Call("conjugateAmplitude",Call("branch",T,p,Call("initial")),z)));
        Formula sum=FiniteSum(p,Call("Path",T),FiniteSum(z,Call("Basis"),
            IfThenElse(Call("Apply",e,p,z),signed,D(0))));
        Formula K=Power(Call("kappa"),Seq(D(2),Star,Call("maxCalls",T)));
        return Disp(All("L",Call("Type"),All("T",Call("Tree",L),All("e",Call("Events",T),
            And(Rel(Call("eventMass",T,e),Eq,Call("realPhysical",x)),
                Rel(nu,Eq,sum),Leq(Call("abs",nu),K))))));
    }
    private static Formula ResourceStatement()
    {
        Formula L=F.Id("L"), T=F.Id("T"), e=F.Id("e"), p=Call("eventMass",T,e);
        Formula K=Power(Call("kappa"),Seq(D(2),Star,Call("maxCalls",T)));
        Formula q=Call("emptyTarget"), w=Call("referenceTarget");
        Formula cq=Seq(Frac,Grp(D(1,3),Plus,D(5),Sqrt,Grp(D(5))),Grp(D(2,2)));
        Formula cw=Seq(Frac,Grp(D(1,9),Plus,D(9),Sqrt,Grp(D(5))),Grp(D(2,2)));
        Formula lower(Formula a,Formula c)=>Leq(Seq(Frac,Grp(D(1)),
            Grp(D(1,1),Star,Parenthesized(Seq(K,Plus,c)))),Call("abs",Seq(p,Minus,a)));
        Formula positive=new Formula.Logic(
            new Formula.Relation(D(0),FormulaRelationOperator.LessThan,p),
            FormulaLogicOperator.Implies,Leq(Power(K,Seq(Minus,D(1))),p));
        return Disp(All("L",Call("Type"),All("T",Call("Tree",L),All("e",Call("Events",T),
            And(Parenthesized(positive),lower(q,cq),lower(w,cw))))));
    }

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Open, Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body, Close);
    private static Formula Rel(Formula a, Formula op, Formula b) =>
        Seq(Open, a, Sp, op, Sp, b, Close);
    private static Formula And(params Formula[] xs) =>
        xs.Aggregate((a,b) => Rel(a,Land,b));
    private static Formula FiniteSum(Formula i, Formula set, Formula term) =>
        Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, set), Sp, term);
    private static Formula ArithmeticStatement()
    {
        Formula L = F.Id("L"), T = F.Id("T"), e = F.Id("e");
        Formula p = Call("eventMass", T, e);
        Formula q = Seq(Frac, Grp(D(1,3), Minus, D(5), Sqrt, Grp(D(5))), Grp(D(2,2)));
        Formula w = Seq(Frac, Grp(D(9), Sqrt, Grp(D(5)), Minus, D(1,9)), Grp(D(2,2)));
        Formula neq(Formula a, Formula b) =>
            new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
        return Disp(All("L", Call("Type"), All("T", Call("Tree", L),
            All("e", Call("Events", T), And(Call("IsIntegral", Call("Int"), p),
                neq(p, q), neq(p, w))))));
    }
    private static Formula Statement()
    {
        Formula T = F.Id("T"), C = F.Id("C"), pi = F.Id("pi"), e = F.Id("e");
        Formula p = F.Id("p"), q = F.Id("q"), z = F.Id("z");
        Formula E = Call("extension", T, C), G = Call("graft", T, E);
        Formula Ep = Call("Apply", E, p), path = Call("Path", T);
        Formula tag = Call("readTag", Call("label", T, p), Call("Apply", C, p), q);
        Formula record = Call("Record", pi, p, tag, Call("label", Ep, q));
        Formula product = Call("MatMul", Call("Op", Ep, q), Call("Op", T, p));
        Formula mass = Call("normSq", Call("Apply", Call("mulVec", product, Call("omegaZero")), z));
        Formula sum = FiniteSum(p, path, FiniteSum(q, Call("Path", Ep),
            FiniteSum(z, Call("Basis"), IfThenElse(Call("Apply", e, record, z), mass, D(0)))));
        Formula r = Call("attach", T, E, p, q);
        Formula semantics = All("p", path, All("q", Call("Path", Ep), And(
            Rel(Call("Op", G, r), Eq, product),
            Rel(Call("Ar", G, r), Eq, Call("Append", Call("Ar", T, p), Call("Ar", Ep, q))),
            Rel(Call("c", G, r), Eq, Rel(Call("c", T, p), Plus, Call("c", Ep, q))),
            Rel(Call("label", G, r), Eq, Call("label", Ep, q)))));
        Formula bound = Rel(Call("L", G), Eq,
            Seq(Operatorname, Grp(F.Id("sup")), Underscore,
                Grp(p, Sp, InMacro, Sp, path), Sp,
                Rel(Call("c", T, p), Plus, Call("L", Ep))));
        Formula law = And(Rel(Call("projectedMass", T, C, pi, e), Eq, sum), bound,
            All("p", path, Call("CutLaw", Call("label", T, p), Call("Apply", C, p))), semantics);
        return Disp(All("T", Call("Tree", Call("Cut")),
            All("C", Call("Continuations", T), All("pi", Call("Nat"),
            All("e", Call("RecordEvent", T), law)))));
    }
}
