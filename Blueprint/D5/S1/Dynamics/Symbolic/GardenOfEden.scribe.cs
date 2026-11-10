using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class GardenOfEdenDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/GardenOfEden.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/wacker2016gardeneden");
    private static Formula Id(string s) => F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Int => Seq(Mathbb, Grp(Id("Z")));
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
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
    private static Formula Word(Formula n) => Arr(Call("Fin", n), Id("A"));
    private static Formula Config => Arr(Int, Id("A"));
    private static Formula Ray => Arr(Nat, Id("A"));
    private static Formula Cast(Formula n) => Call("cast", n);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Rule => Arr(Word(Add(Id("k"), D(2))), Id("A"));
    private static Formula Code(Formula x) => Call("BipermutativeLift.code", Id("h"), x);
    private static Formula Pre => Call("BipermutativePreinjectivity.Preinjective", Id("h"));
    private static Formula Prefix(Formula n) => Call("PrefixGrowthEntropy.prefixCount",
        Call("imageRay", Id("h")), n);
    private static Formula Rate => Seq(Open, Id("n"), Colon, Sp, Nat, Sp, Mapsto, Sp,
        Call("Real.log", Cast(Prefix(Id("n")))), Slash, Cast(Id("n")), Close);
    private static Formula Finite => Seq(Grp(), OpenBracket, Call("Finite", Id("A")), CloseBracket, Comma);
    private static Formula Alphabet => Seq(All("u", Call("Universe")), All("A", Call("Type", Id("u"))));
    private static Formula LocalRule => Seq(All("k", Nat), All("h", Rule));
    private static Formula Not(Formula p) => Seq(Neg, Sp, p);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Moore–Myhill theorem equates surjectivity and finite-difference preinjectivity for every finite-alphabet two-sided local rule.",
        H("The Garden-of-Eden Theorem"), Blocks(
        Paragraph(Text("Let A be any finite alphabet, including the empty and singleton alphabets, and let k be any natural number. "
            + "A local rule h takes a word indexed by Fin(k+2) to a letter of A. The native code sends an arbitrary integer configuration x "
            + "to the configuration whose value at i is h applied to j ↦ x(i+j). "
            + "BipermutativeLift.code, BipermutativeLift.window and BipermutativePreinjectivity.Preinjective refer to the original declarations in the PermutativeLifts namespaces; "
            + "the theorem imposes no permutativity, endpoint injectivity or local bijectivity condition. "
            + "Preinjectivity quantifies over all x,y : Z → A with finite {i | x(i) ≠ y(i)} and identical complete code images.")),
        Describe.Lean(DescribeId.Create("write-word"), DeclarationHandle.Create(Owner + "writeWord"),
            H("Insert a finite word in an arbitrary context"), StatementSource.FromAuthor(St(
                Alphabet, All("n", Nat), All("p", Word(Id("n"))), All("t", Int), All("z", Config), All("i", Int),
                Seq(Call("writeWord", Id("p"), Id("t"), Id("z"), Id("i")), Sp, Eq, Sp,
                    Call("ifThenElse", Seq(Id("t"), Sp, Le, Sp, Id("i"), Sp, Land, Sp,
                        Id("i"), Sp, Lt, Sp, Add(Id("t"), Cast(Id("n")))),
                        Call("p", Call("Fin.mk", Call("Int.toNat", Seq(Id("i"), Sp, Minus, Sp, Id("t"))))),
                        Call("z", Id("i")))))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("writeWord(p,t,z) places p at sites t through t+n-1 and agrees with z elsewhere. "
                    + "Inside the interval the Fin index is (i-t).toNat; its bound follows from t≤i<t+n. "
                    + "The finite word may have length zero, and the ambient configuration has no support restriction."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("erasable-words"), DeclarationHandle.Create(Owner + "exists_erasable_words"),
            H("A finite collision supplies universally replaceable words"), StatementSource.FromAuthor(St(
                Alphabet, LocalRule, Seq(Not(Pre), Sp, Rightarrow),
                Ex("n", Nat), Seq(D(0), Sp, Lt, Sp, Id("n"), Sp, Land),
                Ex("p", Word(Id("n"))), Ex("q", Word(Id("n"))),
                Seq(Id("p"), Sp, Neq, Sp, Id("q"), Sp, Land),
                All("t", Int), All("z", Config),
                Seq(Open, All("j", Call("Fin", Id("n"))),
                    Call("z", Add(Id("t"), Cast(Id("j")))), Sp, Eq, Sp, Call("p", Id("j")), Close, Sp, Rightarrow),
                Seq(Code(Call("writeWord", Id("q"), Id("t"), Id("z"))), Sp, Eq, Sp, Code(Id("z"))))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("No alphabet finiteness is required for this replacement statement. "
                    + "A failure of native preinjectivity gives distinct configurations with a finite disagreement set and equal complete images. "
                    + "Enclose that set in [a,b] and retain the collar [a-(k+1),b+(k+1)]. "
                    + "Every local output window touching the disagreement core lies inside the collar. "
                    + "A window missing the core is unchanged; a window touching it compares with the two original colliding windows. "
                    + "Restrict the colliding configurations to the padded interval and translate that interval to Fin(n). "
                    + "The resulting distinct words p,q have positive common length, and any occurrence of p at any integer site can be replaced by q without changing any output coordinate."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("actual-image-rays"), DeclarationHandle.Create(Owner + "imageRay"),
            H("The actual spatial image language"), StatementSource.FromAuthor(St(
                Alphabet, LocalRule, All("z", Ray),
                Seq(Id("z"), Sp, InMacro, Sp, Call("imageRay", Id("h")), Sp, Iff),
                Ex("x", Config), All("n", Nat),
                Seq(Call("z", Id("n")), Sp, Eq, Sp, Call("BipermutativeLift.code", Id("h"), Id("x"), Cast(Id("n")))))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("imageRay(h) consists exactly of restrictions to natural coordinates of full integer code images. "
                    + "Its prefixCount is the number of Fin(n) words actually realized in those images. "
                    + "For a nonempty alphabet it is nonempty and invariant under the one-sided spatial shift. "
                    + "PrefixGrowthEntropy.prefix_growth_entropy therefore supplies its real logarithmic growth limit."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("strict-image-prefix-loss"), DeclarationHandle.Create(Owner + "strict_image_prefix_loss"),
            H("A finite collision forces strict actual image-prefix growth loss"), StatementSource.FromAuthor(St(
                Alphabet, Finite, LocalRule,
                Seq(D(2), Sp, Le, Sp, Call("Nat.card", Id("A")), Sp, Land, Sp, Not(Pre), Sp, Rightarrow),
                Ex("r", Real),
                Seq(Id("r"), Sp, Lt, Sp, Call("Real.log", Cast(Call("Nat.card", Id("A")))), Sp, Land),
                Call("Tendsto", Rate, Id("atTop"), Call("nhds", Id("r"))))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("Write q=Nat.card(A)≥2. The conclusion gives a real r strictly below log(q), together with convergence of "
                    + "n ↦ log(prefixCount(imageRay(h),n))/n to r. This counts spatial prefixes of complete images; it is not temporal entropy of iterations of code(h).")),
                Paragraph(Text("Take the replaceable words p,q of common length m>0. On n disjoint tiles, replace each occurrence of p by q. "
                    + "The code image is preserved, and every normalized block avoids p. The normalized blocks and a tail of length k+1 determine the first nm output coordinates, "
                    + "so the actual count is at most (card(A)^m−1)^n card(A)^(k+1). "
                    + "Passing to the already existing prefix-growth limit gives r≤log(card(A)^m−1)/m<log(card(A))."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("garden-of-eden"), DeclarationHandle.Create(Owner + "garden_of_eden"),
            H("Surjectivity is equivalent to native preinjectivity"), StatementSource.FromAuthor(St(
                Alphabet, Finite, LocalRule,
                Seq(Call("Function.Surjective", Call("BipermutativeLift.code", Id("h"))), Sp, Iff, Sp, Pre))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("For every universe u, every A : Type(u) with Finite(A), every k : N and every local rule h, "
                    + "the original full code is surjective if and only if the original finite-difference preinjectivity predicate holds. "
                    + "The endpoint uses arbitrary integer configurations and equality of their complete code images. "
                    + "It has no periodic-domain restriction, finite-configuration restriction, alphabet lower bound, or supplied growth or balance condition.")),
                Paragraph(Text("If the code is surjective, every finite word occurs in its image, so actual prefix growth has rate log(card(A)). "
                    + "The strict image-prefix loss from a finite collision contradicts this rate. "
                    + "For the reverse direction, continuity of the native code on the compact finite-alphabet full shift makes its image closed. "
                    + "A point outside the image has a finite cylinder missing the image, and translation supplies a missing word at every site. "
                    + "A missing word of length m bounds the count at length nm by (card(A)^m−1)^n. "
                    + "Meanwhile preinjectivity makes the map from arbitrary source words of length n, inserted into a constant context, "
                    + "injective into image prefixes of length n+k+1. The resulting opposing growth bounds contradict one another. "
                    + "Empty and singleton alphabets are handled directly by subsingleton elimination.")),
                Paragraph(Text("This is the classical Moore–Myhill theorem specialized to the integer full shift. "
                    + "The collar replacement and entropy comparison follow the published Garden-of-Eden argument; the native proof reuses "
                    + "BipermutativeLift.code_shift, the original continuous_code theorem, and PrefixGrowthEntropy.prefix_growth_entropy."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PermutativeLifts/BipermutativePreinjectivity")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/PrefixGrowthEntropy"))]));
}
