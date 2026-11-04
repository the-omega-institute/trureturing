using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class ThreeWayBalanceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative three-way balance on an arbitrary abelian group forces an integer quadratic map and makes every orbit sum invisible in every background.",
        H("Three-way balance on the original group"),
        Blocks(Describe.Lean(
            DescribeId.Create("three-way-quadratic-structure"),
            DeclarationHandle.Create("D5/S3/QuadraticForms/ThreeWayBalance.three_way_quadratic_structure"),
            H("Visible quadratic structure without scalar assumptions"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let A be any additive commutative group, U any additive endomorphism and q any finite real-valued function. Assume pointwise nonnegativity and the displayed balance equation for every pair x,y. No topology, continuity, divisibility, faithfulness, evenness, quadratic law or invertibility of U is assumed. Integer scalar multiplication is the canonical action on the additive group.")),
                Paragraph(Text("For a fixed y, the forward sequence a(n)=q(U iterated n times at y) obeys a(n+2)+a(n+1)=2a(n). The quantity a(n+1)+2a(n) is constant, so nonnegativity bounds all differences. Their absolute values double at each step. An Archimedean growth argument forces the first difference to vanish, giving q(Uy)=q(y). This uses every finite forward iterate and imposes no depth cap.")),
                Paragraph(Text("Comparing balance at y and Uy makes U cubed minus the identity invisible in every background. For d=y+Uy+U squared y, both Ud-d and U squared d-d are invisible. Balance at d consequently gives q(z+d)=q(z)+q(d). The negative recipe -d and nonnegativity force q(d)=0. These are identities of readouts on the original group; no identity U squared plus U plus the identity is imposed on the original labels.")),
                Paragraph(Text("Balance at y,y now gives q(y+y)+2q(-y)=6q(y). Apply this relation to both signs and repeatedly double the group argument. The normalized sum stays bounded while the normalized difference doubles. Nonnegativity forces q(-y)=q(y), hence q(y+y)=4q(y). All division occurs in the real codomain.")),
                Paragraph(Text("Put L=U-U squared and let delta(x,y)=q(x+y)+q(x-y)-2q(x)-2q(y). Applying balance to x+y,x-y and using invisible orbit sums gives 4q(x)+q(x+Ly)+q(x-Ly)=3q(x+y)+3q(x-y). Therefore q(Ly)=3q(y) and delta(x,Ly)=3delta(x,y). Evenness makes delta symmetric, giving delta(Lx,Ly)=9delta(x,y). Additivity of L and q composed with L equal to 3q also give delta(Lx,Ly)=3delta(x,y). Thus the parallelogram defect vanishes.")),
                Paragraph(Text("The resulting parallelogram law is passed directly to TauCeti.QuadraticMap.ofParallelogram with the actual A, real codomain and integer scalar ring. Injective doubling is needed only in the real codomain. The returned quadratic map has underlying function q, so existing polarization and integer quadratic scaling apply without adding real operations to A.")),
                Paragraph(Text("This is the structural part of the original integer-interface representation problem. Positive Gram extension, identification of the null group with the radical, rational localization, real completion, the complex phase, minimality and label-preserving unitary uniqueness require further constructions. No completed Hilbert representation, physical realization, process supply or composite compatibility is asserted here."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        var a = V("A"); var x = V("x"); var y = V("y"); var z = V("z");
        var ux = Call("U", x); var uy = Call("U", y); var uuy = Call("U", uy);
        Formula Q(Formula t) => Call("q", t);
        var balance = All("x", a, All("y", a,
            Equal(Add(Add(Q(Add(x,y)), Q(Add(x,uy))), Q(Add(x,uuy))),
                Add(Multiply(D(3), Q(x)), Multiply(D(3), Q(y))))));
        var nonnegative = All("x", a, Seq(D(0), Sp, Le, Sp, Q(x)));
        var invariant = All("x", a, Equal(Q(ux), Q(x)));
        var invisible = All("z", a, All("y", a,
            Equal(Q(Add(z, Add(Add(y,uy),uuy))), Q(z))));
        var even = All("x", a, Equal(Q(Seq(Minus, x)), Q(x)));
        var parallelogram = All("x", a, All("y", a,
            Equal(Add(Q(Add(x,y)), Q(Sub(x,y))),
                Add(Multiply(D(2), Q(x)), Multiply(D(2), Q(y))))));
        var quadratic = Seq(Exists, Sp, Paren(Seq(V("Q"), Sp, Colon, Sp,
            Call("QuadraticMap", Seq(Mathbb, Grp(V("Z"))), a, Real))), Comma, Sp,
            All("x", a, Equal(Call("Q", x), Q(x))));
        var body = Seq(Paren(nonnegative), Sp, Rightarrow, Sp,
            Paren(balance), Sp, Rightarrow, Sp,
            And(invariant, invisible, even, parallelogram, quadratic));
        return All("A", Call("Type"), Seq(OpenBracket, Call("AddCommGroup", a),
            CloseBracket, Comma, Sp,
            All("U", Call("AddMonoidHom", a, a),
                All("q", Paren(Seq(a, Sp, To, Sp, Real)), body))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Paren(Formula a) => Seq(Open, a, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Paren(Seq(V(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula And(params Formula[] terms) => Seq(
        [.. terms.SelectMany((term, i) => i == 0 ? new[] { Paren(term) }
            : new[] { Sp, Land, Sp, Paren(term) })]);
}
