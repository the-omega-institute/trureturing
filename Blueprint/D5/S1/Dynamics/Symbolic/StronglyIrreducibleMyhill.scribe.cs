using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class StronglyIrreducibleMyhillDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/StronglyIrreducibleMyhill.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/ceccherini2010myhill");
    private static Formula I(string s) => F.Id(s);
    private static Formula Arr(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
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
    private static Formula Mul(Formula a, Formula b) => Rel(a, Star, b);
    private static Formula Pow(Formula a, Formula b) => Seq(Par(a), Caret, Grp(b));
    private static Formula Inv(Formula a) => Pow(a, Seq(Minus, D(1)));
    private static Formula Card(Formula a) => Call("Nat.card", a);
    private static Formula Fin(string s) => All(s, Call("Finset", I("G")));
    private static Formula Cfg => Call("Cfg", I("X"));
    private static Formula Config => Arr(I("G"), I("A"));
    private static Formula TauType => Arr(Cfg, Cfg);
    private static Formula Pat(string s) => Call("PatX", I("X"), I(s));
    private static Formula Value(string x, Formula g) => Call(x, g);
    private static Formula Setup => Seq(All("u", Call("Universe")), All("v", Call("Universe")),
        All("G", Call("Type", I("u"))), All("A", Call("Type", I("v"))),
        OpenBracket, Call("Group", I("G")), CloseBracket, Comma,
        OpenBracket, Call("TopologicalSpace", I("A")), CloseBracket, Comma);
    private static Formula FiniteAlphabet => Seq(OpenBracket, Call("Finite", I("A")), CloseBracket, Comma);
    private static Formula DiscreteAlphabet => Seq(FiniteAlphabet,
        OpenBracket, Call("DiscreteTopology", I("A")), CloseBracket, Comma);
    private static Formula XSetup => All("X", Call("MulSubshift", I("A"), I("G")));
    private static Formula NonemptyX => Call("Set.Nonempty", Call("carrier", I("X")));
    private static Formula SI => Call("SI", I("X"), I("Delta"));
    private static Formula Collar(string s) => Mul(I(s), Inv(I("Delta")));
    private static Formula Agree(string x, string y, string f) => Seq(All("g", I("G")),
        Imp(Rel(I("g"), InMacro, I(f)), Rel(Value(x, I("g")), Eq, Value(y, I("g")))));
    private static Formula Equivariance => Par(Seq(All("g", I("G")), All("x", Cfg),
        Rel(Call("tau", Call("paperShift", I("X"), I("g"), I("x"))), Eq,
            Call("paperShift", I("X"), I("g"), Call("tau", I("x"))))));
    private static Formula Disagreement => Seq(OpenBrace, I("g"), Colon, I("G"), Sp, Mid, Sp,
        Rel(Value("x", I("g")), Neq, Value("y", I("g"))), CloseBrace);
    private static Formula Preinjectivity => Par(Seq(All("x", Cfg), All("y", Cfg),
        Imp(Call("Set.Finite", Disagreement), Imp(Rel(Call("tau", I("x")), Eq, Call("tau", I("y"))),
            Rel(I("x"), Eq, I("y"))))));
    private static Formula Memory => Call("HasMemory", I("X"), I("tau"), I("M"));
    private static Formula St(params Formula[] rows) => Disp(new Formula.Aligned([.. rows.Select(row => Grp(row))]));
    private static DocumentBlock.Describe Desc(string id, string name, string title, Formula statement,
        string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every preinjective continuous equivariant endomorphism of a nonempty strongly irreducible finite-alphabet subshift over a right-counting amenable group is surjective.",
        H("Myhill's theorem for strongly irreducible subshifts"), Blocks(
        Paragraph(Text("Let G and A lie in independent universes. G is any group, and A has a topology. "
            + "A native MulSubshift X is a closed subset of the product G → A invariant under mulShift(g,x)(h)=x(g*h). "
            + "Elements of Cfg(X) retain their membership in this same X. When A is finite and discrete, X is compact. "
            + "No countability, commutativity, finite generation or finite-type assumption is made.")),
        Desc("carrier", "Cfg", "The actual configuration carrier", St(Setup, XSetup,
            Rel(Cfg, Eq, Seq(OpenBrace, I("x"), Colon, Config, Sp, Mid, Sp,
                Rel(I("x"), InMacro, Call("carrier", I("X"))), CloseBrace))),
            "The subtype consists of complete configurations together with their membership in the original subshift.", DescribeRole.Definition),
        Desc("paper-shift", "paperShift", "The left-action convention", St(Setup, XSetup,
            All("g", I("G")), All("x", Cfg), All("h", I("G")),
            Rel(Call("paperShift", I("X"), I("g"), I("x"), I("h")), Eq,
                Value("x", Mul(Inv(I("g")), I("h"))))),
            "This is the paper's action g*x(h)=x(g⁻¹*h). Native invariance under mulShift supplies its membership proof. Products retain their displayed order.", DescribeRole.Definition),
        Desc("strong-irreducibility", "SI", "Finite two-pattern strong irreducibility", St(Setup, XSetup,
            Fin("Delta"), Rel(SI, Iff, Seq(Fin("F"), Fin("K"),
                Imp(Call("Disjoint", Collar("F"), I("K")), Seq(All("x", Cfg), All("y", Cfg),
                    Ex("z", Cfg), And(Agree("z", "x", "F"), Agree("z", "y", "K"))))))),
            "The collar is F*Delta⁻¹. The two patterns are restrictions of configurations already in X; the common configuration must also belong to X. Only finite supports are assumed here. Delta need not be symmetric.", DescribeRole.Definition),
        Desc("occurring-patterns", "PatX", "Globally occurring finite patterns", St(Setup, XSetup, Fin("F"),
            Rel(Pat("F"), Eq, Seq(OpenBrace, I("p"), Colon, Arr(I("F"), I("A")), Sp, Mid, Sp,
                Ex("x", Cfg), All("g", I("F")), Rel(Value("p", I("g")), Eq, Value("x", I("g"))), CloseBrace))),
            "A finite pattern occurs when it extends to one complete configuration in X. This is a relative language, rather than the set of all alphabet words.", DescribeRole.Definition),
        Desc("common-exterior", "common_exterior", "Realize a pattern with a common infinite exterior", St(
            Setup, DiscreteAlphabet, XSetup, Fin("Delta"), Fin("F"), Imp(SI, Seq(All("x", Cfg), All("x0", Cfg),
                Ex("z", Cfg), And(Agree("z", "x", "F"), Seq(All("g", I("G")),
                    Imp(Seq(Neg, Par(Rel(I("g"), InMacro, Collar("F")))),
                        Rel(Value("z", I("g")), Eq, Value("x0", I("g"))))))))),
            "For every occurring F-pattern and every background x0 in X, a configuration z in X realizes that pattern and agrees with x0 at every point outside F*Delta⁻¹. There is no symmetry or identity-membership premise on Delta. Every finite exterior constraint is supplied by SI; compactness of the closed finite-alphabet product realizes all exterior constraints together."),
        Desc("translated-window", "tile", "A left-translated finite window", St(Setup, All("t", I("G")), Fin("E"),
            Rel(Call("tile", I("t"), I("E")), Eq, Seq(OpenBrace, Mul(I("t"), I("e")), Sp, Mid, Sp,
                Rel(I("e"), InMacro, I("E")), CloseBrace))),
            "The tile t*E is the image of E under left multiplication by t.", DescribeRole.Definition),
        Desc("avoiding-patterns", "AvoidPatX", "Occurring patterns avoiding assigned local words", St(
            Setup, XSetup, Fin("C"), Fin("F"), Fin("T"), All("w", Arr(I("T"), Arr(I("C"), I("A")))),
            Rel(Call("AvoidPatX", I("X"), I("C"), I("F"), I("T"), I("w")), Eq,
                Seq(OpenBrace, I("p"), Colon, Arr(I("F"), I("A")), Sp, Mid, Sp, Ex("x", Cfg),
                    And(Seq(All("f", I("F")), Rel(Value("p", I("f")), Eq, Value("x", I("f")))),
                        Seq(All("t", I("T")), Ex("c", I("C")),
                            Rel(Value("x", Mul(I("t"), I("c"))), Neq, Call("w", I("t"), I("c"))))), CloseBrace))),
            "Avoidance at every selected tile belongs to one complete realization in X. The forbidden word may vary with the tile.", DescribeRole.Definition),
        Desc("relative-count", "relative_pattern_bound", "Strict relative admissible-pattern counting", RelativeStatement,
            "Assume X is nonempty, 1 lies in Delta and SI(X,Delta) holds. Each t*E lies inside F, distinct E-tiles are disjoint, C*Delta⁻¹ is contained in E, and every assigned C-pattern occurs in X at its assigned translate. With rho=card(PatX(X,E)), excluding all assigned patterns gives the displayed integer inequality, including empty tile sets and rho=1. In each nonempty exterior fiber there are m≤rho completions. SI supplies one excluded completion without disturbing earlier exclusions. Thus rho*a≤(rho−1)*m for the avoiding completions a; summing the fibers and iterating gives the bound."),
        Desc("memory", "HasMemory", "Memory on the actual subshift", St(Setup, XSetup, All("tau", TauType), Fin("M"),
            Rel(Memory, Iff, Seq(All("x", Cfg), All("y", Cfg),
                Imp(Agree("x", "y", "M"), Rel(Call("tau", I("x"), D(1)), Eq, Call("tau", I("y"), D(1))))))),
            "Agreement on M determines only the output at the identity. Equivariance transports this to agreement on g*M determining the output at g.", DescribeRole.Definition),
        Desc("finite-memory", "finite_memory", "Continuity supplies finite memory", St(Setup, DiscreteAlphabet,
            XSetup, All("tau", TauType), Imp(Call("Continuous", I("tau")), Seq(Ex("M", Call("Finset", I("G"))), Memory))),
            "Pairs with different identity outputs form a compact subset of Cfg(X)×Cfg(X). The open sets where a coordinate differs cover it. A finite subcover supplies M. This derives memory from continuity on X, without extending tau to the full shift."),
        Desc("image-patterns", "ImagePat", "Restrictions of complete images", St(Setup, XSetup, All("tau", TauType), Fin("F"),
            Rel(Call("ImagePat", I("X"), I("tau"), I("F")), Eq,
                Seq(OpenBrace, I("p"), Colon, Arr(I("F"), I("A")), Sp, Mid, Sp, Ex("x", Cfg),
                    All("f", I("F")), Rel(Value("p", I("f")), Eq, Call("tau", I("x"), I("f"))), CloseBrace))),
            "All output coordinates in a counted pattern come from one complete image tau(x), with x and tau(x) both in X.", DescribeRole.Definition),
        Desc("lower-injection", "preinjective_pattern_lower", "A relative lower injection from preinjectivity", LowerStatement,
            "Choose a common-exterior representative z_p for each occurring F-pattern p. Put N=F*Delta⁻¹. If their images agree on U containing N*M⁻¹, locality and the common background make them agree at every point outside U as well. Their complete images are therefore equal. The representatives disagree only inside the finite N, so preinjectivity makes them equal and hence recovers p. This injects the actual relative language into actual image patterns."),
        Desc("myhill", "myhill", "The full arbitrary-group Myhill theorem", MyhillStatement,
            "Give G the discrete measurable structure and assume its native maximal right-counting Foelner filter is nontrivial. A finite witness to SI may be enlarged to contain 1; no symmetry is required. Every continuous equivariant endomorphism of a nonempty X that is injective on finite disagreements is surjective. Empty A has no such nonempty X, while singleton alphabets, singleton subshifts and finite groups are included. The result is the classical Theorem 1.1 of Ceccherini-Silberstein and Coornaert, not a claim of a new mathematical theorem."),
        Paragraph(Text("If the image were proper, compactness would give a nonempty occurring C-pattern missing from all its translates. "
            + "Take E=C*Delta⁻¹ and K={1}∪E∪(Delta⁻¹*M⁻¹). For every finite F, disjoint E-tiles with centers in F have positive density relative to card(F). "
            + "The lower injection uses the single outer window U=F*K. Relative exclusion bounds the image count using rho=card(PatX(X,E)); "
            + "restriction to F and U minus F bounds card(PatX(X,U)) by card(PatX(X,F))*card(A)^card(U minus F). "
            + "Cancel the positive relative source count. If rho=1, any tile contradicts the resulting inequality. If rho≥2, its logarithm forces a fixed positive loss per unit volume. "
            + "The right-boundary ratios on maxFoelner(Gᵐᵒᵖ,Measure.count) tend to zero, so card(U minus F)/card(F) tends to zero. This contradicts that loss. "
            + "Here (op e) • h=h*e. The filter is indexed by arbitrary subsets of G and is eventually supported on finite nonempty sets; no countable subsequence or divergent-volume premise is used.")),
        Paragraph(Text("The finite packing, finite-shape and right-padding estimates come from AmenableGardenOfEden. "
            + "The relative language and the gluing argument extend their use from full shifts to closed strongly irreducible subshifts with constraints. "
            + "Common-exterior realization and the relative counting bound can be reused for other equivariant maps on such a subshift: "
            + "the lower injection compares its occurring source patterns with actual image patterns, while the exclusion bound controls a proper invariant image. "
            + "Each application must retain the same subshift and verify the stated collar, memory and disjoint-tile conditions.")),
        Paragraph(Text("The conclusion is the Myhill direction, from preinjectivity to surjectivity, without a finite-type assumption. "
            + "Under the additional hypothesis IsFiniteType(X), FiniteTypeMoore.moore gives the reverse implication, from surjectivity to preinjectivity, for the same X and continuous equivariant endomorphism tau : Cfg(X) → Cfg(X). "
            + "Combining it directly with myhill yields the equivalence of preinjectivity and surjectivity for this same X and tau under all the stated hypotheses and the additional finite-type hypothesis. "
            + "The amenability premise is the native right-counting Foelner filter condition; no equivalence with an invariant-mean formulation is asserted."))
        )));

    private static Formula RelativeStatement => St(Setup, FiniteAlphabet, XSetup,
        Fin("Delta"), Fin("C"), Fin("E"), Fin("F"), Fin("T"), All("w", Arr(I("T"), Arr(I("C"), I("A")))),
        Seq(NonemptyX, Sp, Rightarrow), Seq(Rel(D(1), InMacro, I("Delta")), Sp, Rightarrow), Seq(SI, Sp, Rightarrow),
        Seq(Rel(Collar("C"), Subseteq, I("E")), Sp, Rightarrow),
        Seq(Par(Seq(All("t", I("T")), Rel(Call("tile", I("t"), I("E")), Subseteq, I("F")))), Sp, Rightarrow),
        Seq(Par(Seq(All("t", I("T")), All("s", I("T")), Imp(Rel(I("t"), Neq, I("s")),
            Call("Disjoint", Call("tile", I("t"), I("E")), Call("tile", I("s"), I("E")))))), Sp, Rightarrow),
        Seq(Par(Seq(All("t", I("T")), Ex("x", Cfg), All("c", I("C")),
            Rel(Value("x", Mul(I("t"), I("c"))), Eq, Call("w", I("t"), I("c"))))), Sp, Rightarrow),
        Rel(Mul(Card(Call("AvoidPatX", I("X"), I("C"), I("F"), I("T"), I("w"))),
            Pow(Card(Pat("E")), Call("card", I("T")))), Le,
            Mul(Card(Pat("F")), Pow(Rel(Card(Pat("E")), Minus, D(1)), Call("card", I("T"))))));
    private static Formula LowerStatement => St(Setup, DiscreteAlphabet, XSetup, Fin("Delta"), Fin("F"), Fin("M"), Fin("U"),
        Seq(SI, Sp, Rightarrow), All("x0", Cfg), All("tau", TauType),
        Seq(Memory, Sp, Rightarrow), Seq(Equivariance, Sp, Rightarrow), Seq(Preinjectivity, Sp, Rightarrow),
        Seq(Rel(Mul(Collar("F"), Inv(I("M"))), Subseteq, I("U")), Sp, Rightarrow),
        Rel(Card(Pat("F")), Le, Card(Call("ImagePat", I("X"), I("tau"), I("U")))));
    private static Formula MyhillStatement => St(Setup, DiscreteAlphabet,
        Seq(Call("MeasurableSpace", I("G")), Colon, Eq, Call("discrete"), Comma),
        Seq(Call("NeBot", Call("maxFoelner", Pow(I("G"), Seq(Mathrm, Grp(I("op")))), Call("Measure.count", I("G")))), Sp, Rightarrow),
        XSetup, Seq(NonemptyX, Sp, Rightarrow),
        Seq(Par(Seq(Ex("Delta", Call("Finset", I("G"))), SI)), Sp, Rightarrow), All("tau", TauType),
        Seq(Call("Continuous", I("tau")), Sp, Rightarrow), Seq(Equivariance, Sp, Rightarrow),
        Seq(Preinjectivity, Sp, Rightarrow), Call("Function.Surjective", I("tau")));
}
