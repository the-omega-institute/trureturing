using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ContinuousObservables;

internal sealed class C0MultipliersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Double centralizers of the full algebra of matrix fields vanishing at infinity are precisely bounded continuous matrix fields, with both pointwise actions and equal norms.",
        H("Multipliers of Matrix Fields Vanishing at Infinity"),
        Blocks(Describe.Lean(
            DescribeId.Create("c0-matrix-multiplier-equivalence"),
            DeclarationHandle.Create("D5/S3/ContinuousObservables/C0Multipliers.source_multiplier_certificate"),
            H("The full matrix multiplier equivalence"),
            StatementSource.FromAuthor(Disp(Statement())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let U be the open real interval (0,1/4) with every point 1/n removed for natural n at least 5. The natural numbers are unbounded: all such reciprocals are removed. Let M be CStarMatrix (Fin 2) (Fin 2) C, the full two by two complex matrix algebra with its C-star operator norm, and let A be the entire complex algebra C0(U,M) of continuous fields vanishing at infinity. Cb(U,M) is the algebra of all bounded norm-continuous fields, with its uniform norm. DC(C,A) denotes the actual Mathlib DoubleCentralizer C A, consisting of bounded complex-linear left and right operators satisfying the centralizer identity.")),
                Paragraph(Text("There exists a complex star-algebra equivalence e from Cb(U,M) onto DC(C,A), and e is an isometry. Thus it preserves addition, multiplication, complex scalars, the unit and star. For every bounded continuous field h, every f in the whole algebra A and every x in U, the left operator of e(h) sends f at x to h(x)f(x), and the right operator sends f at x to f(x)h(x). No compact-support restriction is placed on f.")),
                Paragraph(Text("Conversely, for every double centralizer m there exists exactly one bounded continuous matrix field h having both these actions on every f in A and every x in U. The same field satisfies norm(h)=norm(m), where the first norm is the uniform field norm and the second is the multiplier operator norm. In the displayed formula Actions(m,h) abbreviates these two universally quantified identities. Uniqueness includes the same actions and norm equality.")),
                Paragraph(Text("A compactly supported scalar cutoff, equal to one on a compact neighborhood, gives a matrix section equal to the matrix unit there and of norm at most one. Evaluating a double centralizer on such sections recovers a field pointwise. The centralizer identity forces both actions, independence of the section and uniqueness. On each compact neighborhood the recovered field agrees with the image of one fixed continuous section, proving continuity. The operator estimate gives its uniform bound; the action on arbitrary vanishing fields gives the reverse norm inequality.")),
                Paragraph(Text("Multiplying any field vanishing at infinity by a bounded continuous field on either side again gives a field vanishing at infinity. These products define the bounded linear operators in the reverse construction. Associativity gives the centralizer identity. Pointwise calculations establish multiplication, scalar and star preservation. The reciprocals have zero as their only added accumulation point; adjoining zero makes them compact, which proves that U is open and locally compact.")),
                Paragraph(Text("This statement identifies the multiplier algebra of A. It asserts no zero-extension isomorphism onto an ideal of continuous fields on [0,1], no polynomial-plus-ideal model, no nonunitality theorem, no Gram or mass certificate, and no annihilator, norm-ratio or cone counterexample. Those require additional mathematical statements."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula> { Operatorname, Grp(V(name)), Open };
        for (int i = 0; i < args.Length; i++)
        {
            if (i > 0) parts.AddRange([Comma, Sp]);
            parts.Add(args[i]);
        }
        parts.Add(Close);
        return Seq([.. parts]);
    }
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Par(Seq(V(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Sp, Vert, Sp);
    private static Formula Statement()
    {
        Formula fields = Call("Cb", V("U"), V("M"));
        Formula multipliers = Call("DC", V("C"), V("A"));
        Formula actions = All("h", fields, All("f", V("A"), All("x", V("U"), Seq(
            Call("L", Call("e", V("h")), V("f"), V("x")), Sp, Eq, Sp,
            Call("h", V("x")), Call("f", V("x")), Sp, Land, Sp,
            Call("R", Call("e", V("h")), V("f"), V("x")), Sp, Eq, Sp,
            Call("f", V("x")), Call("h", V("x"))))));
        Formula recovery = All("m", multipliers, Seq(
            Exists, Bang, Sp, Par(Seq(V("h"), Colon, Sp, fields)), Comma, Sp,
            Par(Seq(Call("Actions", V("m"), V("h")), Sp, Land, Sp,
                Norm(V("h")), Sp, Eq, Sp, Norm(V("m"))))));
        return Seq(Exists, Sp,
            Par(Seq(V("e"), Colon, Sp, Call("StarAlgEquiv", V("C"), fields, multipliers))),
            Comma, Sp, Call("Isometry", V("e")), Sp, Land, Sp,
            Par(actions), Sp, Land, Sp, Par(recovery));
    }
}
