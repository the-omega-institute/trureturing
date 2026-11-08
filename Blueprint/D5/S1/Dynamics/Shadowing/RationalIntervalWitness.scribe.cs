using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class RationalIntervalWitnessDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => Seq(Id(s), Open,
        new Formula.LatexSequence([.. xs.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Comma, x })]), Close);
    private static Formula Pow(Formula b, Formula e) => Seq(b, Caret, Grp(e));
    private static Formula Fr(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula St(params Formula[] xs) => Disp(new Formula.Aligned([.. xs]));
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), InMacro, Sp, t, Comma, Sp);
    private static Formula NN => Seq(Mathbb, Grp(Id("N")));
    private static Formula ZZ => Seq(Mathbb, Grp(Id("Z")));
    private static Formula RR => Seq(Mathbb, Grp(Id("R")));
    private static Formula Delta => Fr(D(1), D(2,5,6));
    private static Formula Pr => Seq(Id("P"), Underscore, Grp(Id("r")));
    private static Formula X => Seq(Id("x"), Underscore, Grp(Id("m"), Comma, Id("n")));
    private static Formula At(Formula k) => Seq(X, Open, k, Close);
    private static Formula Center => Seq(D(2), Id("n"));
    private static Formula Shift => Call("shift", Center, X);
    private static Formula Defect => Call("d", Seq(Pow(Id("f"), Center), Open, Call("T", X), Close), Call("T", Shift));
    private static Formula Discrepancy => Call("D", Shift, Call("O", At(Center)));
    private static Formula HalfPow => Pow(Fr(D(1), D(2)), Id("n"));
    private static Formula B => Fr(D(1), Seq(D(2), Open, Pow(D(2), Id("m")), Plus, D(2), Close));
    private static Formula E(Formula k) => Call("e", X, k);
    private static Formula MN => Seq(All("m", NN), All("n", NN));
    private static Formula Range => Seq(D(0), Lt, Id("r"), Le, Sp, Delta);
    private static Formula Regular => Seq(D(3), Le, Sp, Id("m"), Land, Sp, D(1), Le, Sp, Id("n"));
    private static DocumentBlock.Describe Desc(string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create("rational-witness-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S1/Dynamics/Shadowing/RationalIntervalWitness." + name), H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Dynamics/artigue2025shadowing")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The fixed rational interval phase-memory map is not self-tuning on any positive closed restriction, with the original geometric weighted-sum antecedent.",
        H("Rational Interval Every-Radius Witness"), Blocks(
        Paragraph(Text("Use I=[0,1], f(u)=2u/(1+u), delta=1/256 and the full closed domains P_r of integer sequences with e(x,k)=d(x(k+1),f(x(k)))<=r. "
            + "The same maps R and T(x)=action(1+memory(x),R(x)) are those of RationalIntervalRetraction and RationalIntervalPhaseMemory; evaluation on P_r means literal inclusion into P_delta. "
            + "Write O(p)(j)=f^j(p), shift(i,x)(j)=x(i+j), and D(x,y)=sum over all j in Z of 2^(-|j|)d(x(j),y(j)). "
            + "Artigue's Definition 5.1 uses exactly this D with the allowed parameter 1/2. The construction and calculations below are separate from the cited paper.")),
        Paragraph(Text("For natural m and n>=1 let p=2^(-m), q=1/2, and h=f(p)=2/(2^m+1). Define x_(m,n)(k)=p at k=-1, f^(k-2n)(q) for k>=n, and zero otherwise. "
            + "These disjoint cases give zero for k<-1 and for 0<=k<n. Put B(m)=1/[2(2^m+2)]. "
            + "For the formulas below M(x)={k:1/3<x(k)<2/3}; T on a displayed witness always means the same fixed T after inclusion, never a newly chosen map.")),
        Desc("witness_link_errors", "The three exact link errors",
            St(Seq(MN, D(1), Le, Sp, Id("n"), Rightarrow, Sp,
                E(Seq(Minus, D(2))), Eq, Pow(Fr(D(1), D(2)), Id("m")), Land, Sp,
                E(Seq(Minus, D(1))), Eq, Fr(D(2), Seq(Pow(D(2), Id("m")), Plus, D(1))), Land, Sp,
                E(Seq(Id("n"), Minus, D(1))), Eq, Fr(D(1), Seq(Pow(D(2), Id("n")), Plus, D(1))), Land, Sp),
                Seq(All("k", ZZ), Id("k"), Neq, Sp, Minus, D(2), Land, Sp,
                    Id("k"), Neq, Sp, Minus, D(1), Land, Sp, Id("k"), Neq, Sp, Id("n"), Minus, D(1),
                    Rightarrow, Sp, E(Id("k")), Eq, D(0))),
            "The links at -2 and -1 are the isolated early pulse; the link at n-1 enters the genuine tail from zero. All other links are zero or genuine orbit steps. "
                + "The assumption n>=1 makes these three indices distinct, including n=1. The exact support is {-2,-1,n-1}."),
        Desc("witness_marker", "Singleton marker and both boundary neighbors",
            St(Seq(MN, Regular, Rightarrow, Sp, Call("M", X), Eq, OpenBrace, Center, CloseBrace, Land, Sp,
                At(Seq(Center, Minus, D(1))), Eq, Fr(D(1), D(3)), Land, Sp,
                At(Seq(Center, Plus, D(1))), Eq, Fr(D(2), D(3)))),
            "The early point is at most 1/8. For the tail, f^k(q)=2^k/(1+2^k) is strictly between 1/3 and 2/3 exactly when the integer k is zero. "
                + "The coordinates immediately adjacent to 2n are exactly 1/3 and 2/3, and are unmarked under the strict band definition."),
        Desc("witness_defect", "Exact fixed positive defect",
            St(Seq(All("r", RR), Id("r"), Le, Sp, Delta, Rightarrow, Sp,
                MN, Regular, Land, Sp, X, InMacro, Sp, Pr, Rightarrow, Sp, Defect, Eq, B)),
            "At the sole marker q, weight(q)=1/36 and weightedOdds(q)=1/36. The actual finite sums give W(x)=1/36 and A(x)=2^(-2n)/36, hence R(x)=f^(-2n)(q). "
                + "This is a direct evaluation of the defining quotient, rather than an inference from equivariance alone. The origin memory is h, the shifted memory at 2n is zero, and x(2n)=q. "
                + "Thus T(shift(2n,x))=q and f^(2n)T(x)=action(1+h,q). The exact distance is h/(4+2h)=B(m)>0, independent of n."),
        Desc("witness_weightedDistance", "The literal weighted-sum bound",
            St(Seq(MN, D(1), Le, Sp, Id("n"), Rightarrow, Sp, Discrepancy, Le, Sp, HalfPow)),
            "For every integer j>=-n the index 2n+j belongs to the true tail, so the shifted sequence agrees with O(q) on that entire half-line. "
                + "Apply weightedDistance_le_negative_tail to the genuinely infinite sum; all earlier discrepancies together contribute at most 2^(-n). No replacement metric is involved."),
        Desc("T_every_rho_witness", "One early pulse for each positive restriction",
            St(Seq(All("r", RR), Range, Rightarrow, Sp, Exists, Sp, Id("m"), InMacro, Sp, NN, Comma, Sp,
                D(3), Le, Sp, Id("m"), Land, Sp, Pow(D(2), Seq(D(1), Minus, Id("m"))), Lt, Id("r"), Land, Sp),
                Seq(All("a", RR), D(0), Lt, Id("a"), Rightarrow, Sp, Exists, Sp, Id("n"), InMacro, Sp, NN, Comma, Sp,
                    D(1), Le, Sp, Id("n"), Land, Sp, HalfPow, Lt, Call("min", Id("r"), Id("a")), Land, Sp,
                    X, InMacro, Sp, Pr, Land, Sp, Call("Finite", Call("support", Call("linkError", X))), Land, Sp,
                    Discrepancy, Lt, Id("a"), Land, Sp, Defect, Eq, B)),
            "Choose m>=3 once with 2^(1-m)<r, so p<r and h<=2p<r. For any a>0 choose only n>=1 with 2^(-n)<min(r,a). "
                + "The three-error formula puts the whole sequence in the fixed closed P_r, its error support is finite, the original weighted antecedent is strictly less than a, and the defect remains the same positive B(m)."),
        Desc("T_not_self_tuning_on", "Failure of the literal Definition 5.1 on every positive restriction",
            St(Seq(All("r", RR), Range, Rightarrow, Sp, Neg, Sp, Call("SelfTuningOn", Id("r")))),
            "Here SelfTuningOn(r) means: for every epsilon>0 there is a>0 such that, for every x in the full P_r and every i in Z, "
                + "D(shift(i,x),O(x(i)))<a implies d(f^i T(x),T(shift(i,x)))<=epsilon. Fix epsilon=B(m)/2 before a is chosen. The preceding witnesses have strict antecedent and defect B(m)>epsilon for every a>0. "
                + "Together with T_shadowing_map and T_L_shadowing_map this separates the original L-shadowing-map property from self-tuning for this prescribed T. "
                + "Those positive results retain the full closed domain and arbitrary infinitely supported two-sided limit errors. On any positive smaller restriction their scales can be reduced by taking the minimum with its radius. "
                + "The result concerns the specified map; it makes no assertion that the same dynamics lacks other self-tuning selectors.")
        )));
}
