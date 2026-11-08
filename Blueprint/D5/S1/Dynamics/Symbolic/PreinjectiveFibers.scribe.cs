using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class PreinjectiveFibersDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/PreinjectiveFibers.";
    private static readonly LibraryNoteRef BoundaryMechanism =
        LibraryNoteRef.Create("D5/L/Entropy/karitaati2015statistical");
    private static Formula Id(string s) => F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Int => Seq(Mathbb, Grp(Id("Z")));
    private static Formula Arr(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula Call(string s, params Formula[] args)
    {
        var name = new List<Formula>();
        foreach (var part in s.Split('.'))
        {
            if (name.Count > 0) name.Add(Dot);
            name.Add(Id(part));
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
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula Ex(string s, Formula t) => Seq(Exists, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Cast(Formula n) => Call("cast", n);
    private static Formula Config => Arr(Int, Id("A"));
    private static Formula Word(Formula n) => Arr(Call("Fin", n), Id("A"));
    private static Formula Width => Add(Id("k"), D(1));
    private static Formula Rule => Arr(Word(Add(Id("k"), D(2))), Id("A"));
    private static Formula Alphabet => Seq(All("u", Call("Universe")), All("A", Call("Type", Id("u"))));
    private static Formula LocalRule => Seq(All("k", Nat), All("h", Rule));
    private static Formula Pre => Call("BipermutativePreinjectivity.Preinjective", Id("h"));
    private static Formula Code(Formula x) => Call("BipermutativeLift.code", Id("h"), x);
    private static Formula Collars => Call("collarPair", Id("k"), Id("a"), Id("b"));
    private static Formula Fiber => Seq(OpenBrace, Id("x"), Colon, Sp, Config, Sp, Mid, Sp,
        Code(Id("x")), Sp, Eq, Sp, Id("y"), CloseBrace);
    private static Formula Lambda(string j, Formula body) => Seq(Open, Id(j), Colon, Sp,
        Call("Fin", Width), Sp, Mapsto, Sp, body, Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native preinjectivity bounds every complete-output fiber of a finite-alphabet integer block code by card(A)^(2(k+1)).",
        H("Finite Fibers from Preinjectivity"), Blocks(
        Paragraph(Text("Let A : Type(u), k be a natural number and h : (Fin(k+2) → A) → A be arbitrary. "
            + "The original BipermutativeLift.code maps x : Z → A to i ↦ h(j ↦ x(i+j)). "
            + "The original BipermutativePreinjectivity.Preinjective predicate says that configurations differing at finitely many integer coordinates "
            + "and having equal complete code images are equal. No endpoint permutativity or injectivity hypothesis is imposed.")),
        Describe.Lean(DescribeId.Create("two-collars"), DeclarationHandle.Create(Owner + "collarPair"),
            H("Read the two outer collars"), StatementSource.FromAuthor(St(
                Alphabet, All("k", Nat), All("a", Int), All("b", Int), All("x", Config),
                Seq(Call("collarPair", Id("k"), Id("a"), Id("b"), Id("x")), Sp, Eq, Sp, Open,
                    Lambda("j", Call("x", Add(Sub(Id("a"), Cast(Width)), Cast(Id("j"))))), Comma, Sp,
                    Lambda("j", Call("x", Add(Add(Id("b"), D(1)), Cast(Id("j"))))), Close))),
            AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Each component is a word indexed by Fin(k+1). The left collar occupies a-(k+1) through a-1, "
                    + "and the right collar occupies b+1 through b+(k+1). The definition itself allows arbitrary integers a,b and arbitrary alphabets."))),
            DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("finite-family-encoding"), DeclarationHandle.Create(Owner + "finite_family_two_collar_encoding"),
            H("A finite family is separated by two collars"), StatementSource.FromAuthor(St(
                Alphabet, LocalRule, Seq(Pre, Sp, Rightarrow), All("y", Config), All("F", Call("Finset", Config)),
                Seq(Open, All("x", Config), Id("x"), Sp, InMacro, Sp, Id("F"), Sp, Rightarrow, Sp,
                    Code(Id("x")), Sp, Eq, Sp, Id("y"), Close, Sp, Rightarrow),
                Ex("a", Int), Ex("b", Int), Seq(Id("a"), Sp, Le, Sp, Id("b"), Sp, Land),
                Call("Set.InjOn", Collars, Call("coeSet", Id("F"))))),
            AssessedProvenance.FromRepo(BoundaryMechanism), Blocks(
                Paragraph(Text("The alphabet need not be finite or nonempty. For every finite family F of arbitrary integer configurations "
                    + "whose complete images all equal the prescribed y, there exist a≤b such that collarPair(k,a,b) is injective on F.")),
                Paragraph(Text("Choose one distinguishing coordinate for each unequal pair in F and enclose all these coordinates in a single interval [a,b]. "
                    + "Suppose two members x,z agree on both outer collars. Splice x on [a,b] into z outside [a,b]. "
                    + "A local output window missing the interval is unchanged. A window meeting the interval stays within the padded interval, "
                    + "where its exterior entries agree by the collars, so its output equals the corresponding output of x and hence of z. "
                    + "The splice differs from z on only finitely many coordinates. Preinjectivity forces it to equal z, so x and z agree throughout [a,b]. "
                    + "The chosen distinguishing coordinates then force x=z. The interval can depend on F; no single interval for the entire fiber is asserted.")),
                Paragraph(Text("The cited source's Theorem 22 proof, immediately before equation (34), uses preinjectivity and finite-type gluing "
                    + "to determine an interior pattern from boundary and image patterns: a finite splice preserves the complete image and hence equals the original. "
                    + "This is the classical boundary mechanism used here. The exact finite-family collar encoding for arbitrary alphabets is a repository deduction."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("finite-complete-fiber"), DeclarationHandle.Create(Owner + "finite_fiber_ncard_le"),
            H("Every complete-output fiber is uniformly finite"), StatementSource.FromAuthor(St(
                Alphabet, Seq(Grp(), OpenBracket, Call("Finite", Id("A")), CloseBracket, Comma), LocalRule,
                Seq(Pre, Sp, Rightarrow), All("y", Config),
                Seq(Call("Set.Finite", Fiber), Sp, Land),
                Seq(Call("Set.ncard", Fiber), Sp, Le, Sp,
                    Seq(Call("Nat.card", Id("A")), Caret, Grp(D(2), Sp, Cdot, Sp, Open, Width, Close))))),
            AssessedProvenance.FromRepo(BoundaryMechanism), Blocks(
                Paragraph(Text("For every universe u, every A : Type(u) with Finite(A), every natural k, every arbitrary local rule h and every complete output y : Z → A, "
                    + "native preinjectivity implies both explicit finiteness of {x : Z → A | code(h,x)=y} and its Set.ncard bound card(A)^(2(k+1)). "
                    + "The empty and singleton alphabets are included. Configurations and outputs have no finite-support or periodicity restriction, "
                    + "and no balance, finite-fiber or growth certificate is an extra premise.")),
                Paragraph(Text("Apply the finite-family encoding to any finite subset of the fiber. Its target consists of pairs of words of length k+1, "
                    + "so it has card(A)^(k+1)·card(A)^(k+1)=card(A)^(2(k+1)) elements. An injection gives that bound for every finite subset. "
                    + "If the full fiber were infinite, it would contain a finite subset with one more element than the bound, a contradiction. "
                    + "Applying the bound to the now finite full fiber proves the ncard inequality. This is a classical deduction; "
                    + "the bound is not asserted sharp and supplies no effective inversion algorithm.")),
                Paragraph(Text("The exact complete-output fiber finiteness and ncard bound are repository deductions from the classical boundary mechanism, "
                    + "the native code interface and generic finite-set cardinality results. The cited Theorem 22 concerns measure-entropy preservation "
                    + "for a preinjective factor map from a shift of finite type onto a shift; its proof is cited for the mechanism, not as a statement of this exact bound. "
                    + "No literature novelty is claimed.")),
                Paragraph(Text("For an entropy application, equip the finite alphabet with discrete uniformity, put X=A^Z and let Y be the actual range of code(h). "
                    + "The source X is compact, and continuity of code(h) makes Y compact. Let S be spatial shift by one on X, T its restriction to Y, "
                    + "and π : X → Y the code with its codomain restricted to its range. The original code_shift identity makes π a surjective semiconjugacy. "
                    + "Subtype equality identifies each π-fiber with the complete-output fiber above, with the same explicit finiteness and uniform bound. "
                    + "D5.S1.Dynamics.FiniteFiberEntropy.finite_fiber_entropy therefore gives equal covering entropy for S on X and T on Y, including the empty case. "
                    + "These are spatial shift dynamics; this consequence does not concern iteration of code(h)."))),
            DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity"))]));
}
