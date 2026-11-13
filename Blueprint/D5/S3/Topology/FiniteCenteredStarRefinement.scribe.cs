using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FiniteCenteredStarRefinementDocument : IScribeDocumentDefinition
{
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Id(s), [.. xs]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Ex(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mem(Formula a, Formula b) => F.Seq(a, F.Sp, F.InMacro, F.Sp, b);
    private static Formula Inst(string s, Formula x) => F.Seq(F.OpenBracket, Call(s, x), F.CloseBracket, F.Sp);

    private static Formula Statement()
    {
        var xType = Id("X"); var n = Id("n"); var x = Id("x"); var c = Id("c");
        var d = Id("d"); var j = Id("j"); var s = Id("s");
        var setX = Call("Set", xType); var index = Call("Fin", n);
        Formula U(Formula y) => Call("U", y);
        Formula V(Formula y) => Call("V", y);
        var openCover = All("j", index, Call("IsOpen", V(j)));
        var cover = All("x", xType, Ex("j", index, Mem(x, V(j))));
        var open = All("c", xType, Call("IsOpen", U(c)));
        var centered = All("c", xType, Mem(c, U(c)));
        var finiteCover = All("x", xType, Ex("c", xType, And(Mem(c, s), Mem(x, U(c)))));
        var star = All("c", xType, Imp(Mem(c, s), Ex("j", index,
            All("d", xType, Imp(Mem(d, s), Imp(Call("Nonempty", Call("Inter", U(c), U(d))),
                Call("Subset", U(d), V(j))))))));
        return All("X", Id("Types"), F.Seq(Inst("TopologicalSpace", xType),
            Inst("CompactSpace", xType), Inst("TTwoSpace", xType),
            All("n", Id("Nat"), All("V", new Formula.TypeArrow(index, setX),
                Imp(openCover, Imp(cover, Ex("U", new Formula.TypeArrow(xType, setX),
                    Ex("s", Call("Finset", xType), And(open, And(centered, And(finiteCover, star)))))))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite centered open star refinements of finite covers of compact Hausdorff spaces.",
        H("Centered open star refinements"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-centered-star-refinement"),
                DeclarationHandle.Create("D5/S3/Topology/FiniteCenteredStarRefinement.exists_finite_centered_star_refinement"),
                H("Finite construction from continuous coordinates"),
                StatementSource.FromAuthor(F.Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("X is any compact Hausdorff topological space. The original cover V has n members indexed by Fin(n). The natural number n may be zero, in which case the covering hypothesis forces X to be empty. Set and Finset denote subsets and finite subsets. Inter, Subset and Nonempty have their ordinary set-theoretic meanings.")),
                    Paragraph(Text("The refinement U is indexed by all points of X, with c in U(c). A finite set s of these centers covers X. For each c in s there is one original member V(j) containing every selected U(d) that meets U(c). In particular, it contains the centers of those members. This is control of a whole star, rather than only control of each member separately.")),
                    Paragraph(Text("Take a finite continuous partition of unity subordinate to V and put delta = 1 / (4 * (n + 1)). Let U(c) consist of points whose every partition coordinate differs from that of c by less than delta. These sets are open and centered. Compactness supplies the finite subcover.")),
                    Paragraph(Text("At c, some coordinate is greater than three delta: otherwise the sum would be at most 3 * n / (4 * (n + 1)), which is less than one. If U(d) meets U(c), three coordinate differences control every point of U(d). That same coordinate stays positive, so subordination puts all of U(d) in V(j). No metric, dimension or local contractibility assumption on X is used.")),
                    Paragraph(Text("This is a quantitative form of the classical partition-of-unity construction of star refinements. The exact finite construction is derived here from Mathlib's continuous partition of unity; it carries no originality claim. Convex averaging of fiber representatives uses the common original member to control all simultaneously active centers."))),
                DescribeRole.Theorem))));
}
