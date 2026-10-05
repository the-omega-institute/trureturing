using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class CoarseEndpointSpectrumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/CoarseEndpointSpectrum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The nested compensation family has all three coarse endpoints at size one, three at size two, and none thereafter.",
        H("Coarse Endpoint Spectrum"),
        Blocks(
            Describe.Lean(DescribeId.Create("coarse-endpoint-spectrum-route"),
                DeclarationHandle.Create(Prefix + "endpointRoute"), H("Literal small-family routes"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Indices are P0, Xj and Yi, with j and i zero based in Lean. Write qt=L R^(t-1) L L R, bh=R L R^(h-1) L L R and d=R R. At k=1 the lists for P0, X1 and Y0 are respectively [q1,q2], [q2,d] and [q1,b2]. At k=2 the lists for P0, Y0 and Y1 are [q1,b1,q2,q3], [q1,b1,b2,b3] and [q1,b1,q2,b2]. The route continues on the target leaf label and stops on the first merged nonleaf reply. Values of endpointRoute outside these cases impose no safety assertion."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("coarse-endpoint-spectrum-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Exact targets and paid sets"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every k at least one, F is the existing nested compensation family transported from Unit plus Fin(k) plus Fin(k) to Fin(m) by Fintype.equivFin. Thus m=2k+1 and every member has n=3k+13 leaves. E(k,z) abbreviates the condition k=1, or k=2 with z equal to P0 or some Yi. Safe(F,z,qs) means the existing Peels predicate from the full survivor set. This gives the full endpoint spectrum: at k=1 every target, at k=2 exactly P0,Y0,Y1, and at k at least three the empty set.")),
                    Paragraph(Text("R(k,z) denotes endpointRoute(k,e.symm(z)). L(U) denotes the actual leaf-address set; J(pi,U) denotes paid(terminal(pi,U).1); C(pi,U) denotes cost(pi,U). First(R,F,i) is List.find? for the predicate leafLabel(F(i),a)=none. The theorem gives the literal list's safety and a globally correct Strategy with CoarseObservable policy. The target pays exactly its leaves. Each different member pays its leaves together with its first nonleaf exit address, which is actually reached and is outside its leaf set.")),
                    Paragraph(Text("The full target-leaf response table rules out all other targets. For Xj with j at least two, Yi at the two adjacent contraction positions have identical replies on every target leaf, so a safe list cannot split them. For X1 at k at least two, every target-leaf nonleaf group contains at least two competitors. For P0 and each Yi at k at least three, retain every member except X1. The first left slot is constant on this retained set; each other nonempty nonleaf group has at least two retained members. Induction along any proposed safe list preserves the retained set and contradicts the final singleton condition.")),
                    Paragraph(Text("The six small endpoint lists safely remove one competitor at each nonleaf exit. The existing coarse peeling equivalence compiles each list with the complete labelled-leaf verifier and finite acquisition fallback. Its exact paid-set contract supplies the stated bills and endpoint costs."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) =>
        Seq(xs.Select((x, i) => i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);

    private static Formula ResultFormula()
    {
        Formula k = V("k"), z = V("z"), i = V("i"), q = V("q"), qs = V("qs");
        Formula pi = V("pi"), indices = Call("Fin", V("m"));
        Formula tree(Formula j) => Call("F", j);
        Formula route = Call("R", k, z);
        Formula eligible = Call("E", k, z);
        Formula spectrum = Seq(Par(Some("qs", Call("List", V("Address")),
            Call("Safe", V("F"), z, qs))), Sp, Iff, Sp, eligible);
        Formula exit = All("i", indices, Imp(Seq(i, Sp, Neq, Sp, z),
            Some("q", V("Address"), And(
                Eq(Call("First", route, V("F"), i), Call("some", q)),
                Seq(Neg, Sp, Par(Call("Member", q, Call("L", tree(i))))),
                Eq(Call("J", pi, tree(i)), Seq(Call("L", tree(i)), Sp, Cup, Sp,
                    OpenBrace, q, CloseBrace))))));
        Formula realization = Some("pi", V("Strategy"), And(
            Call("CoarseObservable", Call("policy", pi)),
            All("i", indices, Eq(Call("C", pi, tree(i)),
                Seq(D(3), k, Plus, D(14), Minus, Call("indicator", Eq(i, z))))),
            Eq(Call("J", pi, tree(z)), Call("L", tree(z))), exit));
        return All("k", V("Nat"), Imp(Seq(D(1), Sp, Le, Sp, k), All("z", indices,
            And(spectrum, Imp(eligible, And(Call("Safe", V("F"), z, route), realization))))));
    }
}
