using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class FiniteTypeMooreDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/FiniteTypeMoore.";
    private static Formula I(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args)
    {
        var name = new List<Formula>();
        foreach (var part in s.Split('.'))
        {
            if (name.Count > 0) name.Add(Dot);
            name.Add(I(part));
        }
        var items = new List<Formula> { Seq(Operatorname, Grp(Seq([.. name]))), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, I(s), Colon, Sp, t, Comma);
    private static Formula Ex(string s, Formula t) => Seq(Exists, Sp, I(s), Colon, Sp, t, Comma);
    private static Formula Par(Formula p) => Seq(Open, p, Close);
    private static Formula Rel(Formula a, Formula r, Formula b) => Seq(a, Sp, r, Sp, b);
    private static Formula And(Formula a, Formula b) => Rel(Par(a), Land, Par(b));
    private static Formula Imp(Formula a, Formula b) => Rel(Par(a), Rightarrow, b);
    private static Formula Arr(Formula a, Formula b) => Rel(Par(a), To, b);
    private static Formula Mul(Formula a, Formula b) => Rel(a, Star, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Par(a), Caret, Grp(b));
    private static Formula Cfg => Call("Cfg", I("X"));
    private static Formula Setup => Seq(All("u", Call("Universe")), All("v", Call("Universe")),
        All("G", Call("Type", I("u"))), All("A", Call("Type", I("v"))),
        OpenBracket, Call("Group", I("G")), CloseBracket, Comma,
        OpenBracket, Call("TopologicalSpace", I("A")), CloseBracket, Comma);
    private static Formula DiscreteAlphabet => Seq(
        OpenBracket, Call("Finite", I("A")), CloseBracket, Comma,
        OpenBracket, Call("DiscreteTopology", I("A")), CloseBracket, Comma);
    private static Formula XSetup => All("X", Call("MulSubshift", I("A"), I("G")));
    private static Formula TauSetup => All("tau", Arr(Cfg, Cfg));
    private static Formula FiniteType => Call("IsFiniteType", I("X"));
    private static Formula Equivariance => Par(Seq(All("g", I("G")), All("z", Cfg),
        Rel(Call("tau", Call("paperShift", I("X"), I("g"), I("z"))), Eq,
            Call("paperShift", I("X"), I("g"), Call("tau", I("z"))))));
    private static Formula Disagreement => Seq(OpenBrace, I("g"), Colon, I("G"), Sp, Mid, Sp,
        Rel(Call("x", I("g")), Neq, Call("y", I("g"))), CloseBrace);
    private static Formula Preinjectivity => Par(Seq(All("x", Cfg), All("y", Cfg),
        Imp(Call("Set.Finite", Disagreement), Imp(Rel(Call("tau", I("x")), Eq, Call("tau", I("y"))),
            Rel(I("x"), Eq, I("y"))))));
    private static Formula St(params Formula[] rows) => Disp(new Formula.Aligned([.. rows.Select(row => Grp(row))]));
    private static DocumentBlock.Describe Desc(string id, string name, string title, Formula statement,
        string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    private static Formula Replacement => Seq(Ex("C", Call("Finset", I("G"))),
        And(Call("Nonempty", I("C")), Seq(Ex("p", Arr(I("C"), I("A"))), Ex("q", Arr(I("C"), I("A"))),
            And(Rel(I("p"), Neq, I("q")), And(
                Rel(I("p"), InMacro, Call("PatX", I("X"), I("C"))), And(
                Rel(I("q"), InMacro, Call("PatX", I("X"), I("C"))),
                Seq(All("t", I("G")), All("z", Cfg), Imp(
                    Par(Seq(All("c", I("C")), Rel(Call("z", Mul(I("t"), I("c"))), Eq, Call("p", I("c"))))),
                    Seq(Ex("zprime", Cfg), And(
                        Seq(All("c", I("C")), Rel(Call("zprime", Mul(I("t"), I("c"))), Eq, Call("q", I("c")))),
                        And(Seq(All("g", I("G")), Imp(
                            Seq(Neg, Par(Rel(I("g"), InMacro, Call("tile", I("t"), I("C"))))),
                            Rel(Call("zprime", I("g")), Eq, Call("z", I("g"))))),
                            Rel(Call("tau", I("zprime")), Eq, Call("tau", I("z"))))))))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite collision in a finite-type subshift can be replaced uniformly within that same subshift; relative pattern counting gives Moore's implication for strongly irreducible subshifts over arbitrary right-counting amenable groups.",
        H("Moore's theorem for strongly irreducible subshifts of finite type"), Blocks(
        Paragraph(Text("Let G be an arbitrary group and let A be a finite discrete alphabet, in independent universes. "
            + "X is a native closed invariant subshift, and tau is a continuous equivariant endomorphism of its actual carrier Cfg(X). "
            + "All products have the displayed order. There is no countability, finite generation or commutativity hypothesis.")),
        Paragraph(Text("SI(X,Delta) says that any two occurring patterns on finite supports F and K have a common realization in X whenever F*Delta inverse is disjoint from K. "
            + "The original finite Delta may be empty or asymmetric. The counting hypothesis gives G the top measurable space and assumes that maxFoelner(G opposite,Measure.count) is nontrivial. "
            + "The action is (op e) acting on g by g*e. Finite nonempty shapes are taken from this filter over arbitrary subsets of G, without choosing a countable sequence.")),
        Desc("finite-type", "IsFiniteType", "A finite family of native forbidden patterns", St(Setup, XSetup,
            Rel(FiniteType, Iff, Seq(Ex("a", I("A")),
                Seq(I("letI"), Sp, Call("Inhabited", I("A")), Colon, Eq, Call("Inhabited.mk", I("a")), Comma),
                Ex("B", Call("Finset", Call("Pattern", I("A"), I("G")))),
                Rel(Call("carrier", I("X")), Eq, Call("mulForbidden", I("B")))))),
            "The padding value a is chosen existentially. Every member of B has its own arbitrary finite support and gives a forbidden word on that support. "
            + "A configuration belongs to X exactly when no member of B occurs at any left translate. Any finitely supported word is represented by padding it with a outside its support; occurrences inspect only the support. "
            + "An empty family defines the full shift. An empty-support forbidden word has every translate as an occurrence and hence defines an empty carrier. "
            + "No uniform defining-window premise, algorithm or inhabitance instance is supplied separately.", DescribeRole.Definition),
        Desc("replacement", "collision_replacement", "Uniform complete-image replacement in the same subshift", St(
            Setup, DiscreteAlphabet, XSetup, Imp(FiniteType, Seq(TauSetup,
            Imp(Call("Continuous", I("tau")), Imp(Equivariance, Seq(All("x", Cfg), All("y", Cfg),
                Imp(Rel(I("x"), Neq, I("y")), Imp(Call("Set.Finite", Disagreement),
                    Imp(Rel(Call("tau", I("x")), Eq, Call("tau", I("y"))), Replacement))))))))),
            "Neither strong irreducibility nor amenability is used. Let D be the finite disagreement set, and let S contain the finite memory of tau and every forbidden support. "
            + "Take the finite collar C=D union D*S inverse*S, retaining the order d*s inverse*r. Put p=x restricted to C and q=y restricted to C; D is nonempty and contained in C, so p and q are distinct occurring words. "
            + "For a configuration agreeing with x on C, replace C by y. A translated forbidden support touching D lies wholly in C and therefore sees y; a support missing D sees the original configuration. Both avoid every forbidden word. "
            + "The same dichotomy for a translated memory window gives the entire equality of tau-images, using the actual collision tau(x)=tau(y). Equivariance transports the construction to each translate t*C. "
            + "The result stays inside X, equals q on the translated support, and agrees with the original configuration at every point outside it. "
            + "To combine the two local tests, extend the identity output of tau from occurring memory words and pair it with the Boolean test for avoiding all forbidden words. "
            + "This defines a full-shift local rule on A times Bool. On a configuration encoded from X its complete output is (tau(z)(g),true) at every g. "
            + "AmenableGardenOfEden.localMap_piecewise_of_collar preserves this paired output. The Boolean coordinate recovers membership in X before the first coordinate recovers equality of the native tau-images."),
        Paragraph(Text("For finitely many disjoint C-tiles, replace p by q wherever p occurs. Each replacement preserves membership and the complete image, and disjointness preserves exclusions already obtained. "
            + "Choose such a representative for each actual image pattern on F. Its restriction to U determines the image pattern whenever F*M is contained in U. "
            + "This injects the actual image patterns into the occurring U-patterns that avoid p on every selected tile; it is an input-avoidance comparison.")),
        Desc("moore", "moore", "Surjectivity implies preinjectivity", MooreStatement,
            "Write E=C*Delta inverse, enlarging Delta to contain the identity. Pack disjoint E-tiles with centers in a finite right-Foelner shape B. "
            + "Put U=B*K, where the fixed finite K contains the identity, E and the memory M. This supplies containment of the tiles and B*M in U. "
            + "The relative pattern bound, with rho=card(PatX(X,E)), gives card(ImagePat(X,tau,B))*rho^tiles at most card(PatX(X,U))*(rho-1)^tiles. "
            + "Surjectivity identifies the image language with the language of X on B. Padding from B to U costs at most card(A) raised to card(U minus B). Nonemptiness permits cancellation. "
            + "Packing gives positive tile density, while the right-Foelner boundary makes card(U minus B)/card(B) tend to zero. The relative limit contradiction also covers rho=1. "
            + "Thus a nontrivial finite collision is impossible. Combining this implication with StronglyIrreducibleMyhill.myhill gives the Garden-of-Eden equivalence for this same X and tau."),
        Paragraph(Text("Finite and trivial groups are included through the same right-counting filter. Singleton alphabets and singleton carriers need no separate cardinality lower bound. "
            + "The empty alphabet remains quantified; a nonempty carrier would internally supply a letter by evaluation at the identity, so that case has no instance. "
            + "All defining supports and memory windows may be empty or asymmetric. These mathematical implications make no publication-priority claim."))
        )));

    private static Formula MooreStatement => St(Setup, DiscreteAlphabet,
        Seq(Call("MeasurableSpace", I("G")), Colon, Eq, Call("top"), Comma),
        Seq(Call("NeBot", Call("maxFoelner", Pow(I("G"), Seq(Mathrm, Grp(I("op")))),
            Call("Measure.count", I("G")))), Sp, Rightarrow),
        XSetup, Seq(Call("Set.Nonempty", Call("carrier", I("X"))), Sp, Rightarrow),
        Seq(Par(Seq(Ex("Delta", Call("Finset", I("G"))), Call("SI", I("X"), I("Delta")))), Sp, Rightarrow),
        Seq(FiniteType, Sp, Rightarrow), TauSetup,
        Seq(Call("Continuous", I("tau")), Sp, Rightarrow), Seq(Equivariance, Sp, Rightarrow),
        Seq(Call("Function.Surjective", I("tau")), Sp, Rightarrow), Preinjectivity);
}
