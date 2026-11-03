using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Shadowing;

internal sealed class ProgressionExampleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Shadowing/ProgressionExample.";
    private static Formula Id(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] args)
    {
        var items = new List<Formula> { Seq(Operatorname, Grp(Id(s))), Open };
        for (var i = 0; i < args.Length; i++) { if (i > 0) items.AddRange([Comma, Sp]); items.Add(args[i]); }
        items.Add(Close); return Seq([.. items]);
    }
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static DocumentBlock.Describe Thm(string key, string decl, string title, Formula formula, string text, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(key), DeclarationHandle.Create(Owner + decl), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem, resolution);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A weakly mixing compact metric system with neighborhood two-shadowing and without dense nonempty small periodic sets.",
        H("The Full Progression Example for Question 5.6"), Blocks(
        Paragraph(Text("Jonathan Meddaugh and Elyssa Stephens, Shadowing with small diameter sets of bounded cardinality, arXiv:2509.04312v1, Question 5.6 asks: "
            + "Is there a weakly mixing system which has the neighborhood N-shadowing property (N>1) that does not have dense small periodic sets? "
            + "Use the intended nonempty meaning of a small periodic set. The printed definition omits nonemptiness; allowing the empty set would trivialize it. "
            + "The phase space is X={x in {0,1}^N : for every s>=0,p>=1 some j<=p^2+2 has x(s+jp)=0}, with the genuine first-disagreement metric, and the one-sided left shift sigma. "
            + "No homeomorphism hypothesis is imposed by the source's compact metric system definition.")),
        Paragraph(Text("The arithmetic-progression construction, constants and rotation deletion method are attributed to Pro.")),
        Thm("progression-square-transitivity", "progression_shift_product_transitive", "Weak mixing on all nonempty product open sets", St(
            Seq(Forall, Sp, Id("ell"), Colon, Sp, Mathbb, Grp(Id("N")), Sp, To, Sp, Mathbb, Grp(Id("N")), Comma),
            Seq(Open, Forall, Sp, Id("p"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp,
                D(0), Lt, Id("p"), Sp, Rightarrow, Sp, D(3), Le, Call("ell", Id("p")), Close, Sp, Rightarrow),
            Seq(Forall, Sp, Id("U"), Comma, Id("V"), Colon, Sp,
                Call("Set", Seq(Call("ProgressionPoint", Id("ell")), Times, Sp, Call("ProgressionPoint", Id("ell")))), Comma),
            Seq(Call("IsOpen", Id("U")), Sp, Rightarrow, Sp, Call("IsOpen", Id("V")), Sp, Rightarrow,
                Sp, Call("Nonempty", Id("U")), Sp, Rightarrow, Sp, Call("Nonempty", Id("V")), Sp, Rightarrow),
            Seq(Exists, Sp, Id("n"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp, Exists, Sp, Id("z"), Sp, InMacro, Sp, Id("U"), Comma),
            Seq(Open, Call("iterate", Call("progressionShift", Id("ell")), Id("n"), Call("fst", Id("z"))), Comma, Sp,
                Call("iterate", Call("progressionShift", Id("ell")), Id("n"), Call("snd", Id("z"))), Close, Sp, InMacro, Sp, Id("V"))),
            "For this generic statement ell is any natural-valued length function satisfying ell(p)>=3 for every positive p. Set(T) denotes subsets of T and iterate(f,n,x) denotes f^[n](x). For arbitrary nonempty open U,V in ProgressionPoint(ell) times ProgressionPoint(ell), choose contained nonempty open rectangles. Apply open-set mixing to each coordinate pair. "
            + "The maximum of their two thresholds supplies one common hitting time and two points, proving transitivity of the square map."),
        Paragraph(Text("In the endpoint formula, X is ProgressionPoint(quadraticProgressionLength) and sigma is progressionShift(quadraticProgressionLength). "
            + "Set(X) denotes all subsets of X; iterate(f,n,x) denotes f^[n](x), sigma^p denotes p-fold iteration, and image(f,B) denotes the direct image. MapsTo(f,B,B) means image(f,B) is a subset of B. "
            + "NeighborhoodTwoShadowing(sigma) is the existing predicate: for every epsilon>0 there is delta>0 such that every infinite natural-time delta-pseudo-orbit "
            + "admits one same nonempty finite A in X with card(A)<=2 and initial diameter<epsilon, and at every natural time its distance to the shifted set is <epsilon. The minimizing branch may vary with time.")),
        Thm("full-q56-progression-example", "quadratic_progression_example", "The full compact-system existence conclusion", St(
            Seq(Call("Nonempty", Id("X")), Sp, Land, Sp, Call("CompactSpace", Id("X")), Sp, Land),
            Seq(Call("Continuous", Id("sigma")), Sp, Land, Sp, Call("Surjective", Id("sigma")), Sp, Land),
            Seq(Open, Forall, Sp, Id("U"), Comma, Id("V"), Colon, Sp, Call("Set", Seq(Id("X"), Times, Sp, Id("X"))), Comma, Sp,
                Call("IsOpen", Id("U")), Sp, Rightarrow, Sp, Call("IsOpen", Id("V")), Sp, Rightarrow, Sp,
                Call("Nonempty", Id("U")), Sp, Rightarrow, Sp, Call("Nonempty", Id("V")), Sp, Rightarrow),
            Seq(Exists, Sp, Id("n"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp, Exists, Sp, Id("z"), Sp, InMacro, Sp, Id("U"), Comma, Sp,
                Open, Call("iterate", Id("sigma"), Id("n"), Call("fst", Id("z"))), Comma, Sp,
                Call("iterate", Id("sigma"), Id("n"), Call("snd", Id("z"))), Close, Sp, InMacro, Sp, Id("V"), Close, Sp, Land),
            Seq(Call("NeighborhoodTwoShadowing", Id("sigma")), Sp, Land),
            Seq(Exists, Sp, Id("U"), Colon, Sp, Call("Set", Id("X")), Comma, Sp,
                Call("IsClopen", Id("U")), Sp, Land, Sp, Call("Nonempty", Id("U")), Sp, Land),
            Seq(Open, Forall, Sp, Id("p"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp, D(0), Lt, Id("p"), Sp, Rightarrow, Sp,
                Forall, Sp, Id("B"), Colon, Sp, Call("Set", Id("X")), Comma, Sp, Id("B"), Sp, Subseteq, Sp, Id("U"), Sp, Rightarrow),
            Seq(Call("MapsTo", Seq(Id("sigma"), Caret, Grp(Id("p"))), Id("B"), Id("B")), Sp, Rightarrow, Sp,
                Neg, Sp, Call("Nonempty", Id("B")), Close, Sp, Land),
            Seq(Neg, Sp, Open, Exists, Sp, Id("B"), Colon, Sp, Call("Set", Id("X")), Comma, Sp,
                Call("Nonempty", Id("B")), Sp, Land, Sp, Call("IsCompact", Id("B")), Sp, Land, Sp,
                Id("B"), Sp, Subseteq, Sp, Id("U"), Sp, Land, Sp, Exists, Sp, Id("p"), Sp, InMacro, Sp, Mathbb, Grp(Id("N")), Comma, Sp,
                D(0), Lt, Id("p"), Sp, Land, Sp, Call("image", Seq(Id("sigma"), Caret, Grp(Id("p"))), Id("B")), Eq, Id("B"), Close)),
            "The all-zero configuration witnesses nonemptiness, and the closed finite-alphabet carrier is compact. Zero-prepending gives surjectivity, while zero-gap joining gives mixing and hence product transitivity. "
            + "The exact original neighborhood contract holds with the single fixed N=2 for all accuracies and all infinite natural-time pseudo-orbits. "
            + "Take U=[1], containing 10-infinity. For every p>0 it contains no nonempty B with sigma^p(B) subset B; hence it contains no nonempty compact B with sigma^p(B)=B. "
            + "One nonempty open obstruction negates density of nonempty small periodic sets. This is the complete intended existence conclusion, not a finite instance or a conditional mask statement.",
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("meddaugh-stephens-2025-mixing-small-periodic-sets"), ResolutionKind.Proved))
        )));
}
