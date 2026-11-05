using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;
internal sealed class NativeProtocolCalibrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual native calibration and original-event Petz consumers",
        H("Actual native calibration and original-event Petz consumers"),
        Blocks(EmptyPetzNode(), CutMassNode())));

    private static DocumentBlock EmptyPetzNode() => Describe.Lean(
        DescribeId.Create("original-empty-petz-consumer"),
        DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolCalibration.original_empty_petz_consumer"),
        H("Actual faithful calibration and the original empty-input Petz event"),
        StatementSource.FromAuthor(EmptyPetzStatement()),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/stewarttall2025algebraic")),
        Blocks(
            Paragraph(Text("Generality I: the calibration is the actual three-call calculation on the fixed original sixteen-bit golden protocol. Its arithmetic dependency closure contains instance results; this statement supplies no calibration theorem for arbitrary quadratic fields or gate menus.")),
            Paragraph(Text("Use the same full sixteen-bit carrier, root, fourteen addresses, selectors and stop-aware continuations defined in NativeProtocolGraft. The source tree is exactly the chronological three forward calls K3,K2,K1, ending at an active cut. The bijection cut splits shifted bit 2, the original b1, from all fifteen remaining bits. Reduced(v) is the existing partialTraceRight of the rank-one full-carrier matrix, reindexed only by this bijection. This mathematical reduction adds no physical deletion, state preparation or protection of the complement.")),
            Paragraph(Text("The actual gate action on a computational vector has its original diagonal coefficient and one possible center-flip coefficient. Applying it three times to the original root gives a squared times b at 000, a times b squared at 100, zeta times a times c at 001, zeta times b times c at 101, and zeta times b squared at 010, with all other native bits unchanged. Here a=-t, b=-beta times zeta to the fourth, c=-t times zeta cubed. The partial trace contracts equal complement words. It gives chi exactly, with entries t,gamma,conjugate gamma,t squared, where gamma=t squared times beta times conjugate of zeta to the fourth. These weights are computed from that same pure native vector.")),
            Paragraph(Text("The theorem proves that chi is positive definite, has trace one and determinant t to the fourth. Its positive square root is chiRoot=(chi+t squared I)/sqrt(1+2t squared). Positivity of the actual partial trace and uniqueness of the positive square root are reused directly. No faithfulness or square-root identity is assumed. The source tree has exactly three expanded forward calls.")),
            Paragraph(Text("For every full-carrier vector v, summing the two reduced outputs of the actual original b1 projectors gives delta(Reduced(v)), where delta(X) is the diagonal matrix with entries Xii. Each original j output remains a distinct branch; this equality is their mathematical marginal. The empty original root reduces to P0. Its actual j=0 projected vector is the same root and its j=1 vector is zero.")),
            Paragraph(Text("The fixed mathematical Petz map is petz(Y)=sqrt(chi) delta(W Y W) sqrt(chi), with W the existing continuous functional calculus of inverse square root at delta(chi). The existing diagonal functional-calculus theorem identifies W with diag(beta inverse,t inverse). Direct evaluation on the actual empty-root reduction gives petz(Reduced(Omega))11=q=(13-5sqrt(5))/22=t to the fourth divided by (1+2t squared). This is an ideal comparison value, not a native operation or an assumed input probability.")),
            Paragraph(Text("For every complete original continuation table C from the native b1 read to trees of Stop labels, let T=extensionAt(active,C). For the actual terminal event z1=1, summing all acquired paths and terminal complement words, eventMass(T,e) differs from the real part of that same Petz entry and obeys the displayed factor-eleven lower bound. The maximum is that of the complete syntactic tree, including zero, failure and stopped outcomes. The proof consumes original_event_arithmetic and original_event_resource_bounds at this actual T and event. No arbitrary event-mass surrogate, conditioning or success normalization is introduced.")),
            Paragraph(Text("This consumer establishes the three-call calibration and empty-input comparison. The original five-call prefix K3,K2,K1,K10,K13 with every X,Y archive and retained j, its ideal w value, the full identity extension on the complement and original records, failure-zero law and total-variation consumers remain open. NativeProtocolBornNormalization establishes the complete-tree Born law and acquired-event cut trace for every retained-position set. Its original_event_cut_resource_bounds gives the positive-event lower bound and, when that same cut has full rank, the determinant and least-eigenvalue lower bounds of theorem 24.1, including the normalized cut. The semantic identity of the ninth gate power with its inverse remains unproved here."))),
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

    private static DocumentBlock CutMassNode() => Describe.Lean(
        DescribeId.Create("original-event-cut-mass-and-psd"),
        DeclarationHandle.Create("D5/S3/Quantum/Dynamics/NativeProtocolCalibration.original_event_cut_mass_and_psd"),
        H("The same acquired event has its original b1 marginal and positive-mass bound"),
        StatementSource.FromAuthor(CutMassStatement()),
        AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumChannels/chiribella2009networks")),
        Blocks(
            Paragraph(Text("For every original tree T and Boolean predicate e on its complete acquired path, eventReduced sums the actual full-carrier branch reductions over precisely those histories. The cut is the original b1 at shifted position 2, with all fifteen complementary bits retained in the mathematical partial trace. Its trace has real part equal to eventMass(T,historyEvent(e)), and its matrix is positive semidefinite. Zero events and zero branches are included.")),
            Paragraph(Text("If this raw mass is positive, the existing event resource theorem supplies the lower bound kappa to minus twice maxCalls(T). The theorem combines the actual event trace and positivity constructions with the original arithmetic resource bound. It assumes no normalization or faithfulness of this marginal. NativeProtocolBornNormalization establishes unit total mass and the complex trace equality at every retained-position cut. For the same tree, acquired event and retained-position set, original_event_cut_resource_bounds bounds the conjugate determinant by kappa to exponent 2 maxCalls(T) d, where d is the cut dimension. Positive mass and full rank of that same cut imply the reciprocal determinant and least-eigenvalue lower bounds; the normalized cut has the additional reciprocal-mass factor. Full-record reference-history Petz consumers remain open."))),
        DescribeRole.Theorem);

    private static Formula CutMassStatement()
    {
        Formula L=F.Id("L"), T=F.Id("T"), e=F.Id("e");
        Formula mass=Call("eventMass",T,Call("historyEvent",e));
        Formula cut=Call("eventReduced",T,e);
        Formula lower=new Formula.Logic(new Formula.Relation(D(0),FormulaRelationOperator.LessThan,mass),
            FormulaLogicOperator.Implies,Leq(Power(Call("kappa"),Seq(Minus,D(2),Star,Call("maxCalls",T))),mass));
        return Disp(All("L",Call("Type"),All("T",Call("Tree",L),All("e",Call("HistoryEvents",T),
            And(Rel(Call("Re",Call("trace",cut)),Eq,mass),Call("PosSemidef",cut),Parenthesized(lower))))));
    }

    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);

    private static Formula Power(Formula a, Formula b) => Seq(Grp(Parenthesized(a)), Caret, Grp(b));

    private static Formula Leq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);

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
}
